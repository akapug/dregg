//! # `tg_link_page` — the CLIENT of the Telegram cross-platform link ceremony.
//!
//! Served at `GET /tg/link` inside the Telegram Mini App web-view. The SERVER half
//! ([`crate::telegram_miniapp`] `/tg/link/challenge` + `POST /tg/link`) is the trust root; this is
//! the page a human uses to sign a [`webauth_core::link_claim`] with their **root key K** and
//! submit it, binding this Telegram account to the same K they linked from Discord.
//!
//! Two signing paths, because the browser EXTENSION (where K normally lives) is NOT reachable
//! inside Telegram's sandboxed web-view:
//!
//! - **Passkey (#1, the primary path)** — K lives in this web-view's `localStorage`, its 32-byte
//!   seed encrypted (AES-GCM) under a key that only a **WebAuthn passkey** can reproduce (the PRF
//!   extension), with a **passphrase fallback** (PBKDF2) for devices without PRF. K never leaves
//!   the device unencrypted; a passkey tap (or the passphrase) unlocks it to sign.
//! - **Relay (#2, the fallback)** — the page shows the EXACT canonical message bytes to sign; the
//!   human signs them with K wherever it lives (the extension, a CLI) and pastes back the root
//!   pubkey + signature. Zero in-page key handling.
//!
//! ⚠ SECURITY NOTE — the passkey path handles K in the browser. The custody model here (seed
//! generated in-page, wrapped under passkey-PRF / passphrase, stored in `localStorage`) mirrors
//! `extension/src/custody.ts`'s `PasskeyCustody`, but it is CLIENT crypto that this crate cannot
//! unit-test end-to-end (WebAuthn + WebCrypto need a real device). The byte-level correctness that
//! MATTERS — the canonical link-claim message the client signs — is pinned against the Rust
//! `link_claim_message` by [`crate::telegram_miniapp`]'s vector test; the custody wrapping deserves
//! a device + review pass before it is leaned on for anything of value.

use axum::response::Html;

/// `GET /tg/link` — serve the link-ceremony page (static HTML+JS; no auth to serve, exactly like
/// the Mini App shell — the initData gate lives on the `/tg/link/challenge` + `POST /tg/link`
/// calls the page makes).
pub async fn get_tg_link_page() -> Html<&'static str> {
    Html(LINK_PAGE)
}

#[cfg(test)]
mod tests {
    /// The page's JS `linkClaimMessage` MUST build the exact bytes
    /// `webauth_core::link_claim::link_claim_message` (and thus `verify_link_claim`) expect. This
    /// pins the FORMAT the JS mirrors — domain prefix, field order, and exactly four NUL
    /// delimiters — so a client/server drift is a red test, not a silent all-claims-refused bug
    /// (the same class as the initData `signature` regression).
    #[test]
    fn the_page_link_message_format_matches_the_verifier() {
        let msg = webauth_core::link_claim::link_claim_message(
            "telegram",
            "555000111",
            &"cc".repeat(32),
            &"dd".repeat(32),
            "chal-abc",
        )
        .unwrap();
        // DOMAIN(23) + platform(8) + 0 + uid(9) + 0 + custodial(64) + 0 + root(64) + 0 + challenge(8)
        assert_eq!(msg.len(), 23 + 8 + 1 + 9 + 1 + 64 + 1 + 64 + 1 + 8);
        assert!(msg.starts_with(b"dregg-identity-link-v1:telegram\x00555000111\x00"));
        assert_eq!(msg.iter().filter(|&&b| b == 0).count(), 4);
    }

    #[tokio::test]
    async fn the_link_page_serves_both_signing_paths() {
        let axum::response::Html(body) = super::get_tg_link_page().await;
        assert!(body.contains("/tg/link/challenge"));
        assert!(body.contains("linkClaimMessage"));
        assert!(body.contains("dregg-identity-link-v1:")); // the JS domain matches Rust
        assert!(body.contains("Passkey") && body.contains("Paste a signature"));
    }
}

/// The pinned Ed25519 lib (ESM, version-pinned) — the web-view already loads
/// `telegram-web-app.js` from an external origin, so a pinned import is consistent with the shell.
const LINK_PAGE: &str = r####"<!doctype html>
<html lang="en"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>Link your dregg identity</title>
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<style>
  :root { color-scheme: light dark; }
  body { font: 15px/1.5 system-ui, sans-serif; margin: 0; padding: 16px;
         background: var(--tg-theme-bg-color, #fff); color: var(--tg-theme-text-color, #111); }
  h1 { font-size: 1.25rem; margin: .2rem 0 .1rem; }
  .sub { color: var(--tg-theme-hint-color, #777); margin: 0 0 1rem; }
  .card { border: 1px solid var(--tg-theme-hint-color, #ccc); border-radius: 12px; padding: 14px; margin: 12px 0; }
  button { font: inherit; font-weight: 600; width: 100%; padding: 13px; border: 0; border-radius: 10px;
           background: var(--tg-theme-button-color, #2ea6ff); color: var(--tg-theme-button-text-color, #fff);
           margin-top: 8px; cursor: pointer; }
  button.ghost { background: transparent; color: var(--tg-theme-button-color, #2ea6ff);
                 border: 1px solid var(--tg-theme-button-color, #2ea6ff); }
  button:disabled { opacity: .5; }
  textarea, input { width: 100%; box-sizing: border-box; font: 13px/1.4 ui-monospace, monospace;
                    padding: 9px; border-radius: 8px; border: 1px solid var(--tg-theme-hint-color, #ccc);
                    background: var(--tg-theme-secondary-bg-color, #f4f4f5); color: inherit; }
  .mono { font: 12px/1.4 ui-monospace, monospace; word-break: break-all;
          background: var(--tg-theme-secondary-bg-color, #f4f4f5); padding: 8px; border-radius: 6px; }
  .status { margin-top: 10px; font-weight: 600; }
  .ok { color: #1a9d4d; }
  .err { color: #e0294a; }
  .tabs { display: flex; gap: 8px; margin-bottom: 4px; }
  .tabs button { width: auto; flex: 1; padding: 9px; font-size: .9rem; }
  .hidden { display: none; }
  small { color: var(--tg-theme-hint-color, #777); }
</style>
</head><body>
<h1>🔗 Link this Telegram to your dregg identity</h1>
<p class="sub">Sign a one-time claim with your <b>root key</b>. Then Discord-you and Telegram-you are
the same human on boards + leaderboards.</p>

<div id="who" class="card">Loading your Telegram identity…</div>

<div class="tabs">
  <button id="tab-passkey">🔐 Passkey</button>
  <button id="tab-relay" class="ghost">📋 Paste a signature</button>
</div>

<div id="panel-passkey" class="card">
  <b>Sign with a passkey</b>
  <p><small>Your dregg key is created on this device and locked behind a passkey (Face ID / a
  security key). It never leaves the device unencrypted.</small></p>
  <button id="do-passkey">🔐 Create / unlock key &amp; link</button>
  <div id="pass-fallback" class="hidden">
    <p><small>This device has no passkey PRF support — falling back to a passphrase (min 10 chars).</small></p>
    <input id="passphrase" type="password" placeholder="passphrase to lock your key" autocomplete="off">
    <button id="do-passphrase">🔑 Link with passphrase</button>
  </div>
</div>

<div id="panel-relay" class="card hidden">
  <b>Sign it wherever your key lives</b>
  <p><small>Sign these <b>exact bytes</b> with your dregg root key (Ed25519), then paste the root
  public key + signature.</small></p>
  <div>message to sign (hex):</div>
  <div id="msg-hex" class="mono">—</div>
  <input id="root-hex" placeholder="root public key (64 hex)" autocomplete="off">
  <textarea id="sig-hex" rows="2" placeholder="signature (128 hex)"></textarea>
  <button id="do-relay">📋 Submit signature</button>
</div>

<div id="status" class="status"></div>

<script type="module">
import * as ed from "https://esm.sh/@noble/ed25519@2.1.0";

const tg = window.Telegram && window.Telegram.WebApp;
if (tg) { tg.ready(); tg.expand(); }
const initData = (tg && tg.initData) || "";
const $ = (id) => document.getElementById(id);
const setStatus = (msg, cls) => { const s = $("status"); s.textContent = msg; s.className = "status " + (cls||""); };

const enc = new TextEncoder();
const toHex = (u8) => Array.from(u8).map(b => b.toString(16).padStart(2, "0")).join("");
const fromHex = (h) => { const s = h.trim(); const o = new Uint8Array(s.length/2);
  for (let i=0;i<o.length;i++) o[i] = parseInt(s.slice(2*i,2*i+2),16); return o; };
function concatBytes(...arrs){ let n=0; for(const a of arrs) n+=a.length; const o=new Uint8Array(n); let p=0;
  for(const a of arrs){ o.set(a,p); p+=a.length; } return o; }

// The canonical link-claim message — MUST match webauth_core::link_claim::link_claim_message
// byte-for-byte: DOMAIN‖platform‖0‖uid‖0‖custodial_hex‖0‖root_hex‖0‖challenge.
function linkClaimMessage(platform, uid, custodialHex, rootHex, challenge){
  const Z = new Uint8Array([0]);
  return concatBytes(
    enc.encode("dregg-identity-link-v1:" + platform), Z,
    enc.encode(uid), Z, enc.encode(custodialHex), Z, enc.encode(rootHex), Z, enc.encode(challenge));
}

let CTX = null; // {platform, platform_uid, custodial_pubkey_hex, challenge}

async function fetchChallenge(){
  const r = await fetch("/tg/link/challenge", { headers: { "X-Telegram-Init-Data": initData } });
  if (!r.ok) throw new Error("challenge: HTTP " + r.status + " (open this from the bot's Play/link button so Telegram provides identity)");
  return await r.json();
}

async function submit(rootHex, sigHex){
  const body = new URLSearchParams({ root_pubkey_hex: rootHex, signature_hex: sigHex, challenge: CTX.challenge });
  const r = await fetch("/tg/link", { method: "POST",
    headers: { "X-Telegram-Init-Data": initData, "content-type": "application/x-www-form-urlencoded" },
    body: body.toString() });
  const txt = await r.text();
  if (!r.ok) throw new Error("link refused (HTTP " + r.status + "): " + txt);
  return txt;
}

// ── Passkey / passphrase custody of the root key K (seed wrapped in localStorage) ──
const LS_KEY = "dregg_root_k_v1";
const PRF_SALT = enc.encode("dregg-link-prf-v1");

async function aesFromRaw(raw){ // raw: 32 bytes -> AES-GCM key
  return crypto.subtle.importKey("raw", raw, "AES-GCM", false, ["encrypt","decrypt"]); }
async function aesFromPassphrase(pass, salt){
  const base = await crypto.subtle.importKey("raw", enc.encode(pass), "PBKDF2", false, ["deriveKey"]);
  return crypto.subtle.deriveKey({ name:"PBKDF2", salt, iterations:210000, hash:"SHA-256" },
    base, { name:"AES-GCM", length:256 }, false, ["encrypt","decrypt"]); }

async function prfSecret(create){ // returns 32-byte PRF output, or null if unsupported
  try {
    const opts = create ? {
      publicKey: { challenge: crypto.getRandomValues(new Uint8Array(32)),
        rp:{ name:"dregg" }, user:{ id: crypto.getRandomValues(new Uint8Array(16)), name:"dregg", displayName:"dregg" },
        pubKeyCredParams:[{type:"public-key",alg:-7},{type:"public-key",alg:-257}],
        authenticatorSelection:{ residentKey:"required", userVerification:"required" },
        extensions:{ prf:{ eval:{ first: PRF_SALT } } } } }
    : { publicKey: { challenge: crypto.getRandomValues(new Uint8Array(32)), userVerification:"required",
        extensions:{ prf:{ eval:{ first: PRF_SALT } } } } };
    const cred = create ? await navigator.credentials.create(opts) : await navigator.credentials.get(opts);
    const res = cred.getClientExtensionResults();
    if (res && res.prf && res.prf.results && res.prf.results.first) return new Uint8Array(res.prf.results.first);
    return null;
  } catch(e){ return null; }
}

async function unlockSeedPasskey(create){
  const prf = await prfSecret(create);
  if (!prf) return null;               // signal: fall back to passphrase
  const stored = localStorage.getItem(LS_KEY);
  const aes = await aesFromRaw(prf.slice(0,32));
  if (stored){
    const {iv, ct, mode} = JSON.parse(stored);
    if (mode !== "prf") return "MODE_MISMATCH";
    const seed = await crypto.subtle.decrypt({name:"AES-GCM", iv:fromHex(iv)}, aes, fromHex(ct));
    return new Uint8Array(seed);
  } else {
    const seed = ed.utils.randomPrivateKey();
    const iv = crypto.getRandomValues(new Uint8Array(12));
    const ct = new Uint8Array(await crypto.subtle.encrypt({name:"AES-GCM", iv}, aes, seed));
    localStorage.setItem(LS_KEY, JSON.stringify({mode:"prf", iv:toHex(iv), ct:toHex(ct)}));
    return seed;
  }
}
async function unlockSeedPassphrase(pass){
  const stored = localStorage.getItem(LS_KEY);
  if (stored){
    const {iv, ct, salt, mode} = JSON.parse(stored);
    if (mode !== "pass") throw new Error("this device's key is passkey-locked, not passphrase");
    const aes = await aesFromPassphrase(pass, fromHex(salt));
    const seed = await crypto.subtle.decrypt({name:"AES-GCM", iv:fromHex(iv)}, aes, fromHex(ct));
    return new Uint8Array(seed);
  } else {
    const seed = ed.utils.randomPrivateKey();
    const salt = crypto.getRandomValues(new Uint8Array(16));
    const iv = crypto.getRandomValues(new Uint8Array(12));
    const aes = await aesFromPassphrase(pass, salt);
    const ct = new Uint8Array(await crypto.subtle.encrypt({name:"AES-GCM", iv}, aes, seed));
    localStorage.setItem(LS_KEY, JSON.stringify({mode:"pass", iv:toHex(iv), ct:toHex(ct), salt:toHex(salt)}));
    return seed;
  }
}

async function signAndLink(seed){
  const rootPub = await ed.getPublicKeyAsync(seed);
  const rootHex = toHex(rootPub);
  const msg = linkClaimMessage(CTX.platform, CTX.platform_uid, CTX.custodial_pubkey_hex, rootHex, CTX.challenge);
  const sig = await ed.signAsync(msg, seed);
  setStatus("submitting…");
  await submit(rootHex, toHex(sig));
  setStatus("✅ Linked! Telegram-you and Discord-you are now one human.", "ok");
  if (tg && tg.HapticFeedback) tg.HapticFeedback.notificationOccurred("success");
}

// ── UI wiring ──
$("tab-passkey").onclick = () => { $("panel-passkey").classList.remove("hidden"); $("panel-relay").classList.add("hidden");
  $("tab-passkey").classList.remove("ghost"); $("tab-relay").classList.add("ghost"); };
$("tab-relay").onclick = () => { $("panel-relay").classList.remove("hidden"); $("panel-passkey").classList.add("hidden");
  $("tab-relay").classList.remove("ghost"); $("tab-passkey").classList.add("ghost");
  if (CTX) $("msg-hex").textContent = toHex(linkClaimMessage(CTX.platform, CTX.platform_uid, CTX.custodial_pubkey_hex, "<your-root-pubkey-hex>", CTX.challenge)); };

$("do-passkey").onclick = async () => {
  try {
    setStatus("waiting for your passkey…");
    const seed = await unlockSeedPasskey(!localStorage.getItem(LS_KEY));
    if (seed === null){ $("pass-fallback").classList.remove("hidden"); setStatus("no passkey PRF here — use a passphrase below.", "err"); return; }
    if (seed === "MODE_MISMATCH"){ setStatus("this device's key was saved with a passphrase — use that tab.", "err"); return; }
    await signAndLink(seed);
  } catch(e){ setStatus("✗ " + e.message, "err"); }
};
$("do-passphrase").onclick = async () => {
  try {
    const pass = $("passphrase").value;
    if (pass.length < 10){ setStatus("passphrase needs ≥ 10 characters.", "err"); return; }
    setStatus("deriving key…");
    await signAndLink(await unlockSeedPassphrase(pass));
  } catch(e){ setStatus("✗ " + e.message, "err"); }
};
$("do-relay").onclick = async () => {
  try {
    const rootHex = $("root-hex").value.trim().toLowerCase();
    const sigHex = $("sig-hex").value.trim().toLowerCase();
    if (rootHex.length !== 64 || sigHex.length !== 128){ setStatus("root pubkey must be 64 hex, signature 128 hex.", "err"); return; }
    setStatus("submitting…"); await submit(rootHex, sigHex);
    setStatus("✅ Linked! Telegram-you and Discord-you are now one human.", "ok");
  } catch(e){ setStatus("✗ " + e.message, "err"); }
};

// boot
(async () => {
  try {
    CTX = await fetchChallenge();
    $("who").innerHTML = "Telegram <b>#" + CTX.platform_uid + "</b> · this account's dregg key:<div class='mono'>"
      + CTX.custodial_pubkey_hex + "</div>";
    $("msg-hex").textContent = toHex(linkClaimMessage(CTX.platform, CTX.platform_uid, CTX.custodial_pubkey_hex, "<your-root-pubkey-hex>", CTX.challenge));
  } catch(e){ $("who").innerHTML = "<span class='err'>" + e.message + "</span>"; setStatus("", ""); }
})();
</script>
</body></html>
"####;
