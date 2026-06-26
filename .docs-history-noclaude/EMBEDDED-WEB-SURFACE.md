# EMBEDDED-WEB-SURFACE — the browser as a GUEST: a cap-confined web engine the OS bosses around

*Design frontier doc. Present-tense where the dregg side is real (the surface/
shell discipline + the firmament cap model both ship today); clearly-scoped
frontier where it isn't (the libservo embed behind the cap gate; the seL4-PD
renderer). First-principles, no trajectory narrative. Companion to
`docs/STARBRIDGE-V2.md` (the native master interface whose `SurfaceCapability`
+ cap-first shell this reuses verbatim), `docs/SEL4-EMBEDDING.md` (the robigalia
/ seL4 end-state, whose stated blockers this respects), `docs/DREGG-DESKTOP-OS.md`
(the verified-scene compositor teeth), and `docs/CIPHERCLERK-AUDIT.md` /
`macaroon/` (the caveat machinery that mints a surface's bounded authority).*

> **This is the INVERSE of `docs/design-frontiers/WEB-FORWARD.md`. Do not
> conflate them.** They are two opposite host/guest arrangements that happen to
> share the word "surface":
>
> | | host | guest | what dregg provides | status |
> |---|---|---|---|---|
> | **web-forward** (`WEB-FORWARD.md`) | the **browser** | **dregg** | dregg *compiled to wasm* runs a cell/turn world, a light client, and a surface compositor INSIDE a tab; `wasm/src/surface.rs` is a dregg surface painted to a `<canvas>` | shipped (the in-tab world, the light client, the SDK browser door; F1/F2/F3 frontier) |
> | **embedded web surface** (THIS doc) | **dregg / the OS** | the **browser** | a **Servo `WebView` is a cap-confined cell INSIDE the dregg desktop**; its fetches, storage, navigation, JS-bridge, downloads are MEDIATED EFFECTS gated by held caps | the surface/shell discipline + cap model are real; the libservo embed behind the cap gate is a near-term build; the seL4-PD renderer is research |
>
> Web-forward carries dregg OUT to the glass of a browser we don't control.
> The embedded web surface pulls a browser we DO control IN under the ocap
> discipline — dregg "bosses it around." This doc is only the second one.

---

## 0. The one-paragraph thesis

A web page is the canonical piece of **untrusted code that wants ambient
authority** — it wants to fetch any origin, write any cookie, open any window,
read the clipboard, ask for your location. dregg's whole thesis is that there is
*no ambient authority*: every action is a held capability presented to a gate.
The embedded web surface applies that thesis to a whole web engine. **A Servo
`WebView` is opened as a dregg `SurfaceCapability` cell** — the *exact* same
`Target::Surface{cell}` handle `starbridge-v2/src/surface.rs` and
`sel4/dregg-firmament/src/surface.rs` already prove, the same one the native
shell gates every window op on. The shell draws the tab's **trusted-path origin
chrome from the live ledger, never from the page** — the anti-spoof property the
native shell already has (`Shell::identity_of` reads the cell's real lifecycle,
not the surface's self-description), extended to web content so a page cannot
paint its own address bar. And the web engine's **authority-bearing operations
become mediated dregg effects**: libservo surfaces every one of them — network
loads, navigation, new-window requests, permission asks, HTTP auth — as
`WebViewDelegate` callbacks, and **the embedder's impl of that delegate IS the
cap gate**. A fetch the surface's cap does not permit is *refused at the delegate
boundary, visibly*, exactly the way `Shell::share` refuses a widening window
share through the real executor's `DelegationDenied`. A **cipherclerk** mints the
tab's authority as a caveat'd macaroon ("this tab may fetch only `*.example.com`,
no storage, no downloads"), and an iframe or a script-opened window is an
**attenuation that cannot amplify** — the no-amplification guarantee, applied to
web content. The deepest realization is the robigalia / seL4 end-state: Servo as
a **protection-domain component** whose syscalls and IPC are seL4-capability-
mediated, so the renderer cannot reach anything its PD was not handed — but that
end-state is gated on `SEL4-EMBEDDING.md`'s named blocker (a libuv-free Lean
runtime is the *node's* blocker; a Servo PD is its own large port), and this doc
does not overclaim it away.

---

## 1. The surface model — a web surface IS a `SurfaceCapability` cell

We invent **no new windowing model and no new authority model for the browser.**
A web surface is a `SurfaceCapability` over a backing cell, identical in kind to
the cell-view surfaces the native shell already manages (`starbridge-v2/src/
surface.rs`). The only new thing is *what fills the body*: instead of the
`reflect`-projected cell state, the body is a Servo `WebView`'s rendered output,
blitted into the surface's cap-authorized region.

The reuse is exact:

| native shell concept (ships today) | web surface realization | where it lives |
|---|---|---|
| `SurfaceCapability { surface, authority: Capability{ Surface(cell), rights } }` | the same token; `cell` backs a Servo `WebView` instead of a `reflect` cell-view | `surface.rs::SurfaceCapability` (reused verbatim) |
| `Shell::open_cell_view(cell, title) -> cap` | `Shell::open_web_view(cell, initial_url) -> cap` (a new door onto the SAME `open_surface` path) | `shell.rs::open_surface` (the single creation path) |
| every window op (`focus`/`move`/`resize`/`close`/`share`) gated by `authorize(cap)` → the firmament `granted ⊆ held` resolve | identical — a web surface is focused/moved/closed/shared through the same cap-gated ops | `shell.rs::authorize` (the ocap heart) |
| `Shell::compose` builds a `Scene`; `compose_scene` enforces T1/T2/T3 | identical — the web surface's blitted frame is one `CompositedSurface` owning exactly `SurfaceId::region()`; overpaint is T1-UNSAT | `shell.rs::compose_scene`, `compositor.rs` |
| `IdentityLabel` drawn by the SHELL from the live ledger (anti-spoof) | the **trusted-path ORIGIN chrome** — see below | `shell.rs::identity_of` |

### The trusted-path origin chrome is the shell's, never the page's

This is the load-bearing anti-spoof property, and it is *already the native
shell's discipline* — we extend it from "cell lifecycle badge" to "web origin
badge." In the native shell, `Shell::identity_of` computes a surface's identity
badge — the owning cell id + its live lifecycle (`live`/`sealed`/`destroyed`/
`missing`) — **by reading the world ledger, not the surface's self-description**,
so a surface "cannot impersonate another cell's identity" (`shell.rs` doc;
`the_trusted_path_label_tracks_the_live_cell_lifecycle` is green). A dangling
surface reads `missing`, not spoofable (`a_dangling_surface_is_labelled_missing_
not_spoofable`).

For a web surface the identity badge carries the **committed origin and security
state** — the URL the surface is *actually* navigated to (from libservo's
`notify_url_changed`, recorded against the surface cell), its TLS state, and the
cap-scope it holds — **drawn by the shell in trusted chrome the page's DOM cannot
reach.** A page cannot paint a fake `https://yourbank.com 🔒` address bar over
the real one, because:

- the **address/origin badge is a `SceneItem` field the shell computes**
  (`shell.rs::identity_of` extended with the surface's committed URL), painted in
  the shell's title-bar zone, not inside the `WebView` body region;
- the body region the page draws is exactly `SurfaceId::region()`, and the
  compositor's **T1 non-overlap** tooth makes a paint outside it UNSAT — a page
  cannot overpaint the shell's chrome any more than one cell-view can overpaint
  another (`compose_scene` → `compositor::scene_admit`);
- the URL the badge shows is the one libservo's `request_navigation` /
  `notify_url_changed` *committed*, bound to the surface cell — the **T2
  label-binding** is `label_of(owner, source_state_root)`, a function of the
  cell's real state, not chrome the page rendered.

So the same theorem the native shell proves — *the identity a user reads is the
shell's attestation, not the surface's claim* — becomes dregg's structural answer
to **browser-chrome phishing**: the one attack (a page drawing a convincing fake
browser UI) that the open web has no defense against. Here the chrome is outside
the page's reach by construction.

> **Honest scope.** "The page cannot overpaint the chrome" is a dregg theorem
> over the *scene graph* (T1/T2 in `compositor.rs`) AND, at the pixel layer,
> relies on Servo honoring the clip of the region it was handed — the same named
> composition assumption `WEB-FORWARD.md` §7 F3 carries for iframes (dregg
> mediates *authority*; the renderer must honor *isolation*). On the seL4 end-
> state (§5) that isolation becomes a kernel-enforced PD boundary; on a hosted
> desktop it is the embed harness honoring the blit rectangle. Named, not
> laundered.

---

## 2. The authority model / embedding boundary — every web power is a mediated effect

A browser engine's power is exactly its set of **authority-bearing operations**.
We enumerate them and map each to a mediated dregg effect requiring a held cap.
The crucial fact that makes this *real and not aspirational*: **libservo already
surfaces almost every one of these as a `WebViewDelegate` callback**, and a
delegate is "a trait that the embedder installs its own impl for" — so **the
embedding boundary IS the cap gate.** A request the surface's cap does not permit
is refused *at the callback*, before Servo acts.

(libservo method names below are verified against `doc.servo.org/servo/
webview_delegate/trait.WebViewDelegate.html` and the embedder-API PRs, as of
**2026-06-13** — see §4 sources. Servo's API is pre-1.0 and these names move;
treat them as the *shape*, pinned at a date.)

| web authority | libservo delegate hook (the cap gate) | mediated dregg effect / gate | default if embedder is silent |
|---|---|---|---|
| **navigate** (main frame or nested iframe to a URL) | `WebViewDelegate::request_navigation()` | check requested origin ∈ the surface cap's `navigate`-caveat allowlist; commit the new URL to the surface cell (drives the trusted chrome) | Servo **allows** by default → so the gate must AFFIRMATIVELY decide, not rely on the default |
| **network fetch / subresource load** (any HTTP/HTTPS resource, not just navigation) | `WebViewDelegate::load_web_resource()` — "the load may be intercepted… alternate contents loaded by calling `WebResourceLoad::intercept`" | check requested origin ∈ the cap's `fetch`-caveat allowlist; on refusal `intercept` with a cap-denied response (a visible `dregg: blocked by capability` body), else let it continue | continues as normal → gate must intercept-and-decide |
| **open a new window** (`window.open`, target=_blank, script-opened auxiliary) | `WebViewDelegate::request_create_new()` — "web content requests to open a new WebView" | mint a CHILD surface cap that is an **attenuation** of the parent's (§3); the new tab inherits ≤ the opener's authority | **if unhandled, denied** — Servo's safe default already matches the ocap default-deny |
| **permission request** (geolocation, camera/mic, notifications, etc.) | `WebViewDelegate::request_permission()` — "allow or deny… cached value or query the user" | each permission is a distinct cap; granted iff the surface cap carries that permission caveat, else deny (optionally prompt via trusted chrome) | embedder decides; default-deny is the ocap stance |
| **HTTP authentication** (credentials prompt) | `WebViewDelegate::request_authentication()` — "supply credentials for HTTP auth"; "identify the webview that caused a credentials prompt" | route to a cap-scoped credential store (a cipherclerk-held secret), never an ambient keychain; the surface only gets creds its cap names | embedder supplies or denies |
| **storage / cookies / localStorage / IndexedDB** | *no dedicated per-op delegate as of 2026-06-13* — mediated at the **resource layer** (cookies ride `load_web_resource` headers) and the **profile/embedding layer** (Servo's storage is keyed to an embedder-chosen profile dir / config) | bind the surface cell to a **cap-scoped storage partition** (its own profile root); "no storage" = an ephemeral/in-memory partition discarded on close; cookies stripped/forbidden by intercepting `load_web_resource` | see §2.1 — this is the honest seam |
| **file download** | `load_web_resource` (a download is a resource load the embedder routes) → the embedder's save path | a download is an effect that writes a NOTE / file cell; gated by a `download`-caveat naming the allowed sink; "no downloads" = no sink cap | embedder routes the bytes; no sink ⇒ dropped |
| **clipboard** (read/write) | mediated through the embedder's clipboard provider (Servo calls out to the host clipboard the embedder supplies) | clipboard read/write are distinct caps; a tab without the cap gets an empty read / a no-op write — never the host clipboard | embedder supplies the provider (default: none) |
| **JS → host bridge** (page asks the host to do something) | there is **no ambient page→host JS bridge** in Servo (deliberately — §4); the embedder drives JS via `WebView::evaluate_javascript()` HOST→page | a host→page eval is a privileged op the *holder of the surface's control cap* performs; a page cannot call the host except through a bridge the embedder explicitly builds (and that bridge is itself a cap-gated effect) | no bridge unless built; the asymmetry is a feature |

The shape is uniform: **the delegate callback is the powerbox.** Where Servo
already has the hook (navigation, fetch, new-window, permission, auth) the gate is
a clean affirmative check against the surface cap's caveats. Where Servo has no
per-op hook yet (storage, clipboard) the mediation lands one layer out (the
profile partition, the embedder-supplied provider) — named honestly in §2.1 as
the seam, not pretended into a delegate that doesn't exist.

### 2.1 The honest seams in the boundary

Two authorities are **not** a single clean delegate callback today, and saying so
is the discipline:

- **Storage/cookies.** Servo (as of 2026-06-13) exposes no per-write storage
  permission delegate. The faithful mediation is **partition-by-cap**: each web
  surface cell is bound to its own storage profile root, so "this tab gets no
  storage" is realized as an ephemeral partition (discarded on `notify_closed`)
  and "this tab may persist" is a durable partition that is itself a dregg cell
  (a NOTE-backed store). Cookie suppression is enforceable *now* by stripping
  `Set-Cookie` / `Cookie` in `load_web_resource`; finer-grained per-key
  localStorage gating is a **frontier item** that needs either a Servo
  storage-delegate (an upstream ask) or a script-layer shim (§4 content-script
  path). Stated as work, not a wall.

- **JS→host bridge.** This is a *non-seam that reads like a seam*: Servo
  deliberately does **not** expose a page-reachable JS API to the host (§4). That
  asymmetry is exactly what the ocap discipline wants — the host reaches into the
  page (`evaluate_javascript`), the page cannot reach out except through a bridge
  the embedder *constructs as an explicit cap-gated effect*. So "the JS bridge is
  a mediated effect" is true by the absence of an ambient one: any bridge is
  opt-in and gateable.

---

## 3. The cipherclerk's role — minting, attenuating, and delegating a tab's authority

A surface cap answers *which window*; a **cipherclerk** answers *what that window
may do* — it mints the tab's authority as a **caveat'd macaroon** and is the
thing that makes "this tab may fetch only `*.example.com`, no storage, no
downloads" a first-class, checkable object rather than a config flag. dregg's
cipherclerk is real and wired (`docs/CIPHERCLERK-AUDIT.md`; the
`AgentCipherclerk` the starbridge-v2 CIPHERCLERK tab drives through real
`mint`/`attenuate`/`delegate`/`discharge` with no reimplemented crypto;
`macaroon/` is an HMAC-authenticated append-only caveat chain whose `verify`
rejects a removed/tampered caveat).

The web surface's authority is a macaroon whose **caveats name the mediated
effects of §2**:

```
root cap (the surface's authority), then attenuating caveats:
  fetch  ⊆ { https://*.example.com }      # load_web_resource allowlist
  navigate ⊆ { https://*.example.com }    # request_navigation allowlist
  storage = ephemeral                     # partition-by-cap, discarded on close
  downloads = none                        # no download sink cap
  permissions = {}                        # request_permission default-deny
  new-window: inherit-attenuated          # request_create_new mints a child ≤ this
  exp = <epoch deadline>                  # the tab's authority expires
```

When the delegate of §2 fires, it **discharges the surface's macaroon against the
request**: `request_navigation` to `https://evil.com` parses to a navigate
request that the `navigate ⊆ {*.example.com}` caveat *prohibits*, so the delegate
returns deny and the shell shows the refusal in trusted chrome. This is the same
`discharge` verdict (caveat evaluation over the HMAC chain) the CIPHERCLERK tab
already runs for the native loop — the web surface is one more `Access` the
caveats check `prohibits` against (`macaroon/src/access.rs`).

### The no-amplification guarantee, applied to web content

The keystone. **An iframe, or a script-opened window, is an ATTENUATION of its
opener — it cannot amplify.** When page content calls `window.open` (or embeds an
iframe whose loads route through the same surface), `request_create_new` fires and
the embedder mints the child surface's macaroon as **the parent's macaroon plus
strictly-narrowing caveats** — never wider. A child tab opened by an
`*.example.com` page that tries to claim `fetch ⊆ {*}` is refused for the same
structural reason `Shell::share` refuses a widening window share: it routes
through the real `Effect::GrantCapability` attenuation gate, and a widening
delegation is `DelegationDenied` (`shell.rs::share`; `a_narrowing_window_share_
commits_and_a_widening_share_rejects` is green; the firmament's own
`real_executor_rejects_widening_surface_share`). The macaroon layer enforces the
same monotonicity: a macaroon only ever gains caveats, and `verify` rejects a
chain with a caveat removed (`macaroon/src/caveat_chain_diff.rs`
`removal_breaks_tail`). So **a sub-frame can only ever hold ≤ the authority of the
frame that spawned it** — the web's "an ad iframe inherits the page's ambient
reach" footgun is closed by construction. The delegation surface is the same one
the cipherclerk already exposes (`delegate` produces a real signed, recipient-
targeted token); the recipient here is the child `WebView`'s surface cell.

---

## 4. Two control surfaces — the embedding API (primary) and WebExtensions (researched)

There are two candidate ways to "boss the browser around." We assess both
honestly. **The embedding API is PRIMARY**; WebExtensions are a complementary
content-script surface *if and where Servo supports them* — and the researched
reality is that Servo does **not** support them today.

### 4.1 The libservo embedding API — the strong "boss it around" path (RECOMMENDED PRIMARY)

This is the path §2 already describes, and it is strong *precisely because it does
not depend on the page's cooperation or on an extension runtime.* The `WebView` /
`WebViewDelegate` API is libservo's first-class embedder surface, modeled
explicitly on "the delegates in Apple's WebKit API" — the embedder installs an
impl of the delegate trait and Servo calls *out* to it at every authority point.
Verified capabilities of this API as of **2026-06-13**:

- **navigation policy** — `request_navigation()` decides per-load (main frame +
  nested iframes); "NavigationRequests are accepted by default" (so the gate must
  affirmatively decide).
- **arbitrary resource interception** — `load_web_resource()`; per the Feb-2025
  embedder-API work, "embedders can now intercept **any** request, not just
  navigation," and may `WebResourceLoad::intercept` to substitute contents. This
  is the fetch/cookie/download chokepoint.
- **new-window control** — `request_create_new()` for `window.open`; **denied if
  unhandled** (the safe default the ocap child-mint refines).
- **permission control** — `request_permission()` (allow/deny, cache or prompt).
- **HTTP auth** — `request_authentication()`, and the embedder "can now identify
  the webview that caused an HTTP credentials prompt."
- **host→page scripting** — `WebView::evaluate_javascript()` runs JS in the page
  and returns the result to the embedder asynchronously (merged in
  `servo/servo#35720`). Note the direction: **host drives page**, not the reverse.
- **handle-based lifecycle** — the webview handle's lifetime controls the
  webview's, "giving the embedder full control over exactly when webviews are
  created and destroyed" — which is exactly what `revoke` (drop the surface cap,
  drop the WebView handle, the glass goes dark) needs.

This is a clean cap gate: every authority Servo can exercise, it asks the
embedder for first, and the embedder is dregg's cap check. **Recommend this as
the primary and load-bearing control surface.**

### 4.2 WebExtensions — the researched reality (as of 2026-06-13)

ember flagged uncertainty here; the research result is clear and worth stating
precisely with its date:

> **As of 2026-06-13, Servo has NO native WebExtensions support, and it is not a
> near-term roadmap item.** Servo reached its first tagged release (v0.0.1) in
> October 2025 (Igalia / Linux Foundation Europe); its public posture treats
> "web extensions, permissions, and other features" required to build a *full*
> browser as **future work the embedding API is designed to eventually
> accommodate, not present functionality.** Crucially, the Servo team has stated
> they **deliberately do not want to expose a JS API directly from Servo**, and
> that a JavaScript/extension API would be **a third-party project layered on the
> embedding API**, not a core engine feature. The 2025 roadmap discussion does
> not commit to a WebExtensions implementation; the engine's investment is in
> growing and *simplifying* the embedding (`WebView`/`WebViewDelegate`) API.

Sources (dated): Servo embedding-API design discussion (mozbrowser-killing
thread; "future work… web extensions, permissions"; "don't want to expose a JS
API directly from Servo" → a third-party JS-API project); Servo "This month"
Feb-2025 (the WebViewDelegate / WebResourceRequested embedder API); Servo
2024-in-review (2025-01-31) and the v0.0.1 release coverage (Oct 2025); the
WebViewDelegate rustdoc (`doc.servo.org`). The WebExtensions *absence* is an
absence-of-evidence across all official posts plus the explicit "extensions = a
third-party layer" design stance — a careful negative, not a guess.

**Implication for the design.** Because Servo lacks a WebExtensions runtime, the
"content-script" style of mediation (a privileged script injected into every page
to police DOM-level behavior the embedder can't see from outside) is **not
available off-the-shelf.** The honest options, in order of soundness:

1. **Don't depend on it.** The embedding-API path (§4.1) mediates *authority* —
   the actual fetches, navigations, windows, permissions — from *outside* the
   page, which is strictly stronger and more trustworthy than an in-page content
   script (a content script shares the page's renderer and is a weaker confinement
   boundary). This is why §4.1 is primary: it needs nothing Servo lacks.
2. **Build the content-script surface on `evaluate_javascript`.** Where a *DOM-
   level* policy is genuinely needed (e.g. hiding an element, observing a
   mutation), the embedder can inject a privileged script via
   `WebView::evaluate_javascript()` at document-start — a *host-controlled*
   injection, not a page-installed extension. This is exactly the "third-party JS
   layer on the embedding API" Servo points at, realized as a cap-gated host
   effect: the injected script runs on the *holder of the surface's control cap's*
   authority, and what it may do is bounded by the surface's caveats.
3. **A real WebExtensions runtime is a research frontier** — it would mean either
   Servo upstreaming one (not on the 2025 roadmap) or dregg building an extension
   host atop `evaluate_javascript` (a large effort). Named as research, not
   claimed.

**Recommendation:** the embedding API (§4.1) is the primary, sound control
surface and the basis of the whole authority model in §2–§3. A content-script
surface, if needed, is built host-side on `evaluate_javascript` (option 2),
*complementing* the embedding API — never depended upon, and never described as
"Servo WebExtensions" because that does not exist today.

---

## 5. The robigalia / seL4 end-state — Servo as a confined protection domain

The deepest realization of "boss it around" is structural, not behavioral: make
the renderer a **protection-domain component the OS confines**, so that the
mediation of §2 is backstopped by the kernel. In the decomposed seL4 framing
(`SEL4-EMBEDDING.md` §1), the OS is a Microkit/CAmkES assembly of PDs whose
seL4-capability boundaries *are* the trust boundaries. A web surface adds one PD:

- a **`renderer` PD running Servo**, whose entire authority is the set of seL4
  caps its parent handed it: a framebuffer/region cap (it can paint *only* its
  granted region — the kernel-enforced version of the §1 T1 clip), an IPC
  endpoint to a **`web-broker` PD**, and *nothing else* — no NIC cap, no storage
  device cap, no other PD's memory;
- the **`web-broker` PD** holds the network/storage caps and is where the §2
  delegate gates live: the renderer cannot fetch, it can only *ask the broker*
  over IPC, and the broker discharges the surface's macaroon (§3) before touching
  the NIC cap it solely holds. This is the §2 boundary made into an address-space
  boundary: "a fetch the cap doesn't permit is refused" becomes "the renderer
  *physically cannot* reach the network except through the broker, which refuses."

This is the seL4-native form of the CapDesk / "thin untrusted renderer holding
only the granted facets" pattern: the renderer is the untrusted facet-holder, the
broker is the powerbox, and **the renderer cannot reach anything its PD was not
handed** — capabilities all the way down (`SEL4-EMBEDDING.md` §6: seL4 caps
isolate the PDs; dregg caps mediate within). The dregg cap graph (the surface's
macaroon) and the seL4 cap graph (the renderer PD's c-list) agree by construction:
the macaroon's `fetch` caveat is the *policy* the broker enforces; the absence of
a NIC cap in the renderer's c-list is the *mechanism* that makes the policy
unbypassable.

> **Respect the blockers — do not overclaim.** `SEL4-EMBEDDING.md` is explicit
> that the **executor PD** is blocked on a libuv-free, IO-free Lean runtime port
> (its §2, §7 — "the one true blocker," weeks-to-a-quarter of specialist work),
> and that today's boots are the **verifier / rbg-userspace** PDs, not the
> executor. A **Servo `renderer` PD is its own large port on top of that** —
> Servo is a multi-MB Rust codebase assuming a substantial `std`/POSIX surface
> (sockets, threads, GPU access); running it as an seL4 PD is a research effort of
> comparable or greater magnitude to the Lean-runtime port, gated on the same
> `std`-on-seL4 substrate (`crates/experimental/sel4-musl`,
> `sel4-root-task-with-std`) that §2/§5 of that doc flag as in-progress, **plus**
> a GPU/framebuffer-cap story. So §5 here is the **architectural end-state and the
> reason the §2 model is the right shape** (it pre-factors cleanly into PD +
> broker), NOT a claim that a confined-Servo seL4 image exists or is near. It is
> research, sequenced behind the executor-PD blocker.

---

## 6. Honest scope — real today / near-term build / research

Per the repo discipline (docs teach what-is; name seams as work not walls; never
trajectory-narrativize), the boundary between what ships, what's buildable, and
what's research:

**Real today (the foundation this reuses, all green):**

- **The `SurfaceCapability` model** — a window IS a `Capability{ Surface(cell),
  rights }`; opening mints it, every op is gated by the firmament `granted ⊆ held`
  resolve, a forged cap is refused on every op (`starbridge-v2/src/surface.rs`,
  `shell.rs`; `a_forged_capability_is_refused_every_op`). A web surface is one
  more `SurfaceKind` on this exact model.
- **The trusted-path identity chrome** — drawn by the shell from the live ledger,
  not the surface; tracks the backing cell's real lifecycle; a dangling surface
  reads `missing`, not spoofable (`shell.rs::identity_of`; two green tests). The
  web origin badge is this property carried to the committed URL.
- **The no-amplification guarantee on surfaces** — a widening window share is
  rejected by the real executor (`shell.rs::share` → `DelegationDenied`; green).
  Child-tab attenuation reuses it.
- **The verified-scene compositor** — T1 non-overlap / T2 label-binding / T3
  focus-exclusivity over the scene graph (`compositor.rs`, `shell.rs::
  compose_scene`/`present`). A web surface's blit is one `CompositedSurface`.
- **The cipherclerk + macaroon machinery** — real mint/attenuate/delegate/
  discharge over an HMAC caveat chain that rejects removed/tampered caveats
  (`docs/CIPHERCLERK-AUDIT.md`, `macaroon/`). The tab's authority is one such
  macaroon.

**Near-term build (buildable now against existing code + a current libservo):**

- **A libservo embed behind the `WebViewDelegate` cap gate.** Add
  `Shell::open_web_view(cell, url)` onto the existing `open_surface` path; host a
  `WebView` whose `WebViewDelegate` impl is the cap check of §2 (navigation /
  fetch-interception / new-window / permission / auth all have hooks today);
  bind the surface cell to a cap-scoped storage partition; mint the tab's
  authority as a cipherclerk macaroon; blit the WebView frame into
  `SurfaceId::region()`. This contends with nothing in the kernel/circuit cutover
  (it is a starbridge-v2 + new-dep slice). The one genuinely new integration is
  the WebView↔region blit and the delegate↔macaroon discharge wiring; everything
  it gates against already exists. **This is the headline near-term deliverable.**
- **Host-side content-script injection** via `evaluate_javascript` at
  document-start, *if* a DOM-level policy is needed — option 4.2(2),
  complementary, not depended on.

**Research (named, not claimed):**

- **A confined-Servo seL4 `renderer` PD** (§5) — gated on `SEL4-EMBEDDING.md`'s
  Lean-runtime blocker *and* a Servo-on-seL4 port *and* a GPU/framebuffer-cap
  story. The architectural end-state; the reason §2 is the right shape; not near.
- **Per-key storage / localStorage delegate mediation** — needs an upstream Servo
  storage-delegate or a script-layer shim; today's sound mediation is
  partition-by-cap + cookie-stripping at `load_web_resource` (§2.1).
- **A full WebExtensions runtime** — Servo has none as of 2026-06-13 and it is not
  on the 2025 roadmap; building one atop `evaluate_javascript` is a large effort
  (§4.2). The sound path needs none of it.

---

*A web page is untrusted code that wants ambient authority; dregg's answer is that
there is none. The embedded web surface opens a Servo `WebView` as the same
`SurfaceCapability` cell the native shell already gates, draws the origin chrome
from the ledger so a page cannot paint its own address bar, and turns every web
authority — fetch, navigate, new-window, permission, auth — into a mediated effect
the libservo `WebViewDelegate` asks the embedder for, where the embedder is the
cap check. A cipherclerk mints the tab's authority as a caveat'd macaroon, and an
iframe or popup is an attenuation that cannot amplify — the no-amplification
guarantee, on web content. The embedding API is the primary, sound control
surface; Servo has no WebExtensions today, so a content-script surface, if needed,
is built host-side on `evaluate_javascript`, never depended upon. The deepest form
is a Servo protection-domain the kernel confines so the renderer physically cannot
reach what its PD was not handed — the architectural end-state, honestly gated on
the seL4 blockers, not claimed near. The browser becomes a guest under the ocap
discipline: dregg bosses it around.*
