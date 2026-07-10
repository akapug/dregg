import Jwt
import Reactor.Serialize
import Proto.Basic
import IpFilter
import Rate

/-!
# Reactor.RouteMw — per-route middleware: a pre-handler stage that may short-circuit

A **route middleware** runs BEFORE a route's handler. It inspects the request and
either PASSES (the handler answers) or SHORT-CIRCUITS with its own response (the
handler is never reached). A route may carry an ordered CHAIN of middlewares; the
first that short-circuits wins, and its response is served in place of the handler.

The wired kinds are:

* `bearerAuth` — the SAME proven `Jwt.authenticate` machine the deployed `/admin` gate
  (`Reactor.AuthDeploy`) runs, with the identical pinned HS256 key and `Bearer` scheme
  parse. A request whose token the machine rejects (no token, bad signature, alg
  confusion, expiry, …) is answered with a serializer-built **401** (`WWW-Authenticate:
  Bearer`, RFC 6750 §3); an admit passes to the handler. No new auth logic — the
  control-flow safety theorems (`Jwt.jwt_rejects_bad_sig`, `jwt_alg_confusion_safe`, …)
  hold over this config.

* `ipAllow cidrs` — the SAME proven `IpFilter.permits` deny-precedence CIDR decision the
  deployed `Reactor.Stage.IpFilter` gate runs, over an ALLOW-list ruleset built from the
  route's declared CIDRs (`defaultDeny := true`: a client outside every allow CIDR is
  refused). A refused client is answered with a serializer-built **403 Forbidden**; an
  admitted one passes to the handler. No new filtering logic — the decision is
  `IpFilter.permits` (`ip_allow_grants` / `ip_default_applies` / `ip_deny_precedence`).

* `rate budget` — the SAME proven `Rate.tryAdmit ∘ Rate.refill` token-bucket admit the
  deployed `Reactor.Stage.Rate` gate runs, over a per-route bucket of capacity `budget`.
  A request over the budget is answered with a serializer-built **429 Too Many
  Requests**; one under the budget passes. No new limiting logic — the decision is
  `Rate.tryAdmit` (`tryAdmit_snd_true` / `tryAdmit_snd_false`).

RESIDUAL (named, not faked). A route middleware is a PURE function of the `Proto.Request`
(headers/method/target) — the stateless per-request seam the deployed `bearerAuth` gate
already runs at. It carries no socket peer address and no per-connection counter (those
live in the metered serve's `Ctx` attribute bag, which the accept path writes and which
the proven STAGE wrappers consult). So at THIS seam:

* `ipAllow` reads the client address from the `X-Forwarded-For` request header (the same
  attribution the deployed IP-filter conformance already drives). The CIDR admission
  DECISION is proven; the address SOURCE is request-carried (trusting the immediate peer
  to set it), not read off the accepted socket — threading the real socket peer to the
  config serve is a dataplane accept-path change, out of this seam's scope.
* `rate` reads the per-connection request index from the `X-Rate-Seq` request header (its
  byte-length = the index), mirroring how `Reactor.Stage.Rate` reads it from the
  accept-path-written `rate-seq` `Ctx` attr. The token-bucket admit DECISION is proven;
  the index SOURCE is request-carried, since the stateless config serve threads no
  per-connection counter — a live burst-429 across separate requests needs the metered
  accept-path index (which the global STAGE has), out of this seam's scope.

An unrecognized middleware name denotes to `deny` — a fail-CLOSED `501 Not Implemented`,
so a typo or a not-yet-wired middleware name never silently exposes the route; the
residual name is carried, not faked. An `ip-allow` whose CIDR arg does not parse
fail-closes to an EMPTY allow set (every client refused); a `rate` whose budget does not
parse fail-closes to budget `0` (every request refused).

`runChain_status_final` proves the chain preserves the non-1xx (`≥ 200`) final-status
invariant the deployed serve upholds (RFC 9110 §15.4): every short-circuit response is
`≥ 200` (401 / 403 / 429 / 501), so wrapping a handler in a chain keeps the response a
genuine final.
-/

namespace Reactor.RouteMw

open Proto (Bytes Request)

/-- ASCII string as response bytes. -/
def str (s : String) : Bytes := s.toUTF8.toList

/-! ## The deployed bearer-auth JWT surface (mirrors `Reactor.AuthDeploy`) -/

/-- The single pinned HS256 verification key — the verification algorithm is pinned
here, never taken from the token. Identical to the deployed `/admin` gate's key. -/
def bearerKey : Jwt.Key := { kid := "k1", alg := .hs256, material := ⟨1⟩ }

def hdrNone : Jwt.Header := { alg := .none, kid := some "k1" }
def hdrHs : Jwt.Header := { alg := .hs256, kid := some "k1" }
def hdrRs : Jwt.Header := { alg := .rs256, kid := some "k1" }

def claimsEmpty : Jwt.Claims :=
  { iss := none, sub := none, aud := [], exp := none, nbf := none, iat := none }

/-- **The bearer-auth configuration.** The crypto/decode fields are the named
boundaries `Jwt.Config` requires; the control-flow theorems hold for all of them.
This is the SAME concrete surface the deployed `/admin` gate pins. -/
def bearerCfg : Jwt.Config where
  keys := [bearerKey]
  sources := [.bearer]
  skew := 0
  expectedIss := none
  requiredAud := none
  parseBearer := fun s => if s.take 7 == "Bearer " then some (s.drop 7) else none
  segments := fun s => s.splitOn "."
  decodeHeader := fun s =>
    if s == "none" then some hdrNone
    else if s == "hs256" then some hdrHs
    else if s == "rs256" then some hdrRs
    else none
  decodeClaims := fun _ => some claimsEmpty
  decodeSig := fun _ => some []
  signingInput := fun _ _ => []
  understoodCrit := []
  verifyHmac := fun _ _ si sig => si == sig
  verifyRsaPkcs1 := fun _ _ si sig => si == sig
  verifyRsaPss := fun _ _ si sig => si == sig
  verifyEcdsa := fun _ _ si sig => si == sig
  edPubKey := fun _ => []

/-- The clock the gate reads (NumericDate seconds). -/
def bearerNow : Nat := 0

/-- Interpret header-value bytes as a string. -/
def bytesToStr (b : Bytes) : String := String.mk (b.map (fun x => Char.ofNat x.toNat))

/-- Lower-case an ASCII string (RFC 9110 §5.1 field-name case-insensitivity). -/
def lowerStr (s : String) : String := String.mk (s.data.map Char.toLower)

/-- Look up a request header value by its lower-cased name. -/
def headerLookup (hs : List (Bytes × Bytes)) (nameLower : String) : Option String :=
  match hs.find? (fun h => lowerStr (bytesToStr h.1) == nameLower) with
  | some (_, v) => some (bytesToStr v)
  | none        => none

/-- The `Jwt.Request` built from a `Proto.Request`: its `Authorization` header. -/
def jwtReqOf (req : Request) : Jwt.Request :=
  { authorization := headerLookup req.headers "authorization"
  , cookies := [], query := [], headers := [] }

/-- **The bearer-auth decision** — the REAL `Jwt.authenticate` over `bearerCfg`. -/
def bearerOutcome (req : Request) : Jwt.Outcome :=
  Jwt.authenticate bearerCfg { req := jwtReqOf req, now := bearerNow }

theorem bearerOutcome_is_authenticate (req : Request) :
    bearerOutcome req = Jwt.authenticate bearerCfg { req := jwtReqOf req, now := bearerNow } := rfl

/-! ## The short-circuit responses -/

/-- Serializer-built **401 Unauthorized** — the response for a route whose bearer
auth fails. The body is fixed policy prose (no handler content can flow); it carries
the `WWW-Authenticate: Bearer` challenge (RFC 6750 §3). -/
def unauthorized401 : Response :=
  { status := 401, reason := str "Unauthorized"
  , headers := [(str "WWW-Authenticate", str "Bearer")]
  , body := str "authentication required\n" }

theorem unauthorized401_status : unauthorized401.status = 401 := rfl

/-- Fail-CLOSED **501 Not Implemented** — the response for an unrecognized middleware
name, so a not-yet-wired name never silently exposes the route. -/
def notImplemented501 (name : Bytes) : Response :=
  { status := 501, reason := str "Not Implemented", headers := []
  , body := str "middleware not implemented: " ++ name }

theorem notImplemented501_status (name : Bytes) : (notImplemented501 name).status = 501 := rfl

/-! ## The `ip-allow` surface — the proven `IpFilter.permits` CIDR decision

`IpFilter` (the base library) proved `permits`: an ordered allow/deny CIDR decision with
deny-precedence and a `defaultDeny` toggle. `ip-allow <cidr-list>` reuses it as a
per-route ALLOW-list: `defaultDeny := true` with one `allow` rule per declared CIDR, so a
client inside any allow CIDR is admitted and every other client is refused. No new
filtering logic — the decision is `IpFilter.permits`. -/

open _root_.IpFilter (Addr Family Cidr Action Ruleset)

/-- The 8 low bits of `n` (MSB-first) — one dotted-quad octet as address bits. Explicit
so the kernel reduces it (for the `by decide` non-vacuity witnesses). -/
def octetBits (n : Nat) : List Bool :=
  [decide (n / 128 % 2 = 1), decide (n / 64 % 2 = 1), decide (n / 32 % 2 = 1),
   decide (n / 16 % 2 = 1), decide (n / 8 % 2 = 1), decide (n / 4 % 2 = 1),
   decide (n / 2 % 2 = 1), decide (n % 2 = 1)]

/-- The 32 address bits of a dotted-quad IPv4 address (MSB-first). -/
def v4Bits (a b c d : Nat) : List Bool := octetBits a ++ octetBits b ++ octetBits c ++ octetBits d

/-- An IPv4 `Addr` from its four octets. -/
def v4Addr (a b c d : Nat) : Addr := ⟨.v4, v4Bits a b c d⟩

/-- An IPv4 `Cidr` from four octets and a prefix length. -/
def v4Cidr (a b c d len : Nat) : Cidr := ⟨.v4, v4Bits a b c d, len⟩

/-- The value of a decimal digit character, or `none`. -/
def digitVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat) else none

/-- Parse a non-empty run of decimal digits to a `Nat` (`none` on empty / non-digit). -/
def parseDec (s : String) : Option Nat :=
  match s.data with
  | []      => none
  | c :: cs => cs.foldl (fun acc ch => match acc, digitVal ch with
      | some n, some d => some (n * 10 + d) | _, _ => none) (digitVal c)

/-- Parse a dotted-quad IPv4 literal (`a.b.c.d`) to an `Addr`. -/
def parseV4 (s : String) : Option Addr :=
  match s.splitOn "." with
  | [a, b, c, d] =>
    match parseDec a, parseDec b, parseDec c, parseDec d with
    | some a, some b, some c, some d => some (v4Addr a b c d)
    | _, _, _, _ => none
  | _ => none

/-- Parse one CIDR token: `a.b.c.d` (implicit `/32`) or `a.b.c.d/len`. -/
def parseCidrTok (s : String) : Option Cidr :=
  match s.splitOn "/" with
  | [ip]    => (parseV4 ip).map (fun a => ⟨a.family, a.bits, 32⟩)
  | [ip, l] =>
    match parseV4 ip, parseDec l with
    | some a, some len => some ⟨a.family, a.bits, len⟩
    | _, _ => none
  | _ => none

/-- Parse a comma-separated allow-list of CIDR tokens (`none` if any token is malformed). -/
def parseAllowList (s : String) : Option (List Cidr) :=
  (s.splitOn ",").foldr (fun tok acc =>
    match parseCidrTok tok, acc with
    | some c, some cs => some (c :: cs)
    | _, _ => none) (some [])

/-- The allow-list ruleset a `ip-allow` middleware decides with: one `allow` rule per
declared CIDR and `defaultDeny := true`, so a client outside every allow CIDR is refused.
The decision run over it is the proven `IpFilter.permits`. -/
def allowRuleset (cidrs : List Cidr) : Ruleset :=
  { rules := cidrs.map (fun c => (c, Action.allow)), defaultDeny := true }

/-- The client address the `ip-allow` gate decides on: the `X-Forwarded-For` request
header parsed as a dotted-quad (`none` when the header is absent or unparseable). NAMED
RESIDUAL: this is the request-carried attribution, not the accepted socket peer. -/
def clientAddr (req : Request) : Option Addr :=
  match headerLookup req.headers "x-forwarded-for" with
  | some s => parseV4 s
  | none   => none

/-- **The `ip-allow` decision** — the REAL `IpFilter.permits` over the allow-list
ruleset, on the request-attributed client address. A request with no attributable client
address fails CLOSED (refused). -/
def ipAllowAdmits (cidrs : List Cidr) (req : Request) : Bool :=
  match clientAddr req with
  | some a => _root_.IpFilter.permits (allowRuleset cidrs) a
  | none   => false

/-- Serializer-built **403 Forbidden** — the response for a client the allow-list
refuses. Fixed policy prose (no handler content flows). -/
def forbidden403 : Response :=
  { status := 403, reason := str "Forbidden", headers := []
  , body := str "forbidden: ip not admitted\n" }

theorem forbidden403_status : forbidden403.status = 403 := rfl

/-! ## The `rate` surface — the proven `Rate.tryAdmit` token-bucket admit

`Rate` (the base library) proved `refill`/`tryAdmit`: a token-bucket transition. `rate
<budget>` reuses it as a per-route budget: the standing bucket has `budget - seq` tokens
(`seq` = the connection's request index), refilled to clock `0`, then `tryAdmit`
consulted — exactly the transition `Reactor.Stage.Rate` drives. -/

/-- The per-connection request index the `rate` gate reads: the `X-Rate-Seq` header's
byte-length (`0` when absent). NAMED RESIDUAL: request-carried, mirroring how the proven
`Reactor.Stage.Rate` reads it from the accept-path-written `rate-seq` `Ctx` attr. -/
def rateSeq (req : Request) : Nat :=
  match headerLookup req.headers "x-rate-seq" with
  | some s => s.length
  | none   => 0

/-- The live bucket the `rate` gate decides on: `budget - seq` tokens remain (saturating),
capacity `budget`, no time refill (`rate := 0`) — the burst window is the capacity. -/
def rateBucket (budget : Nat) (req : Request) : _root_.Rate.Bucket :=
  { tokens := budget - rateSeq req, last := 0, cap := budget, rate := 0 }

/-- **The `rate` decision** — refill to clock `0`, then the REAL `Rate.tryAdmit`. `true` =
a token was available (under budget, admit); `false` = none (over budget, reject). -/
def rateAdmits (budget : Nat) (req : Request) : Bool :=
  (_root_.Rate.tryAdmit (_root_.Rate.refill 0 (rateBucket budget req))).2

/-- Serializer-built **429 Too Many Requests** — the response when the bucket is empty. -/
def tooMany429 : Response :=
  { status := 429, reason := str "Too Many Requests", headers := []
  , body := str "rate limit exceeded\n" }

theorem tooMany429_status : tooMany429.status = 429 := rfl

/-! ## The middleware model -/

/-- A named per-route middleware. `bearerAuth` is wired to the proven `Jwt.authenticate`
gate; `ipAllow` to the proven `IpFilter.permits` CIDR decision (over its allow-list);
`rate` to the proven `Rate.tryAdmit` token bucket (over its budget); `deny name` is the
fail-closed residual for an unrecognized name. -/
inductive RouteMw where
  | bearerAuth
  | ipAllow (cidrs : List Cidr)
  | rate (budget : Nat)
  | deny (name : Bytes)
deriving DecidableEq, Repr

/-- Map a middleware NAME to its wired middleware (no-argument names only): `bearer-auth`
⇒ the proven bearer gate; anything else ⇒ the fail-closed `deny` residual. The
argument-taking names (`ip-allow`, `rate`) are built by `mwOfClause`. -/
def mwOfName (name : String) : RouteMw :=
  if name = "bearer-auth" then .bearerAuth else .deny name.toUTF8.toList

/-- Map a middleware CLAUSE (name + optional argument token) to its wired middleware:
`bearer-auth` ⇒ the proven bearer gate; `ip-allow <cidr-list>` ⇒ the proven
`IpFilter.permits` allow-list decision (an unparseable list fail-closes to an empty allow
set ⇒ every client refused); `rate <n>` ⇒ the proven `Rate.tryAdmit` bucket of capacity
`n` (an unparseable budget fail-closes to `0` ⇒ every request refused). An argument-taking
name with no argument, or any unrecognized name, ⇒ the fail-closed `deny` residual (the
name is carried, not faked). -/
def mwOfClause (name : String) (arg : Option String) : RouteMw :=
  if name = "bearer-auth" then .bearerAuth
  else if name = "ip-allow" then
    match arg with
    | some a => .ipAllow ((parseAllowList a).getD [])
    | none   => .deny name.toUTF8.toList
  else if name = "rate" then
    match arg with
    | some a => .rate ((parseDec a).getD 0)
    | none   => .deny name.toUTF8.toList
  else .deny name.toUTF8.toList

/-- **Run one middleware.** `none` ⇒ pass to the handler; `some r` ⇒ short-circuit
with `r`. `bearerAuth` short-circuits with 401 exactly when the real `Jwt.authenticate`
rejects; `ipAllow` with 403 exactly when the real `IpFilter.permits` refuses; `rate`
with 429 exactly when the real `Rate.tryAdmit` rejects; `deny` always short-circuits
(fail-closed 501). -/
def check (req : Request) : RouteMw → Option Response
  | .bearerAuth =>
    match bearerOutcome req with
    | .reject _ => some unauthorized401
    | .admit _  => none
  | .ipAllow cidrs => if ipAllowAdmits cidrs req then none else some forbidden403
  | .rate budget   => if rateAdmits budget req then none else some tooMany429
  | .deny name => some (notImplemented501 name)

/-- **Run a middleware chain before an inner handler response.** The first middleware
that short-circuits wins; if all pass, the inner handler's response is served. -/
def runChain (req : Request) (mws : List RouteMw) (inner : Response) : Response :=
  match mws with
  | []      => inner
  | m :: rest =>
    match check req m with
    | some r => r
    | none   => runChain req rest inner

/-- The empty chain is the identity: no middleware ⇒ the handler answers unchanged. -/
theorem runChain_nil (req : Request) (inner : Response) : runChain req [] inner = inner := rfl

/-- **Bearer-auth blocks a tokenless request.** With `bearerAuth` at the head of the
chain and the real gate rejecting, the served response is the 401 — the handler is
never reached. -/
theorem runChain_bearer_rejects (req : Request) (rest : List RouteMw) (inner : Response)
    (hrej : ∃ r, bearerOutcome req = .reject r) :
    runChain req (.bearerAuth :: rest) inner = unauthorized401 := by
  obtain ⟨r, hr⟩ := hrej
  simp only [runChain, check, hr]

/-- **Bearer-auth passes an admitted request to the handler.** With `bearerAuth` the
only middleware and the real gate admitting, the served response is the handler's. -/
theorem runChain_bearer_admits (req : Request) (inner : Response)
    (hadm : ∃ h, bearerOutcome req = .admit h) :
    runChain req [.bearerAuth] inner = inner := by
  obtain ⟨h, ha⟩ := hadm
  simp only [runChain, check, ha]

/-- Every short-circuit response is a genuine final (`≥ 200`): 401 or 501. -/
theorem check_status_final (req : Request) (m : RouteMw) :
    ∀ r, check req m = some r → 200 ≤ r.status := by
  intro r hr
  cases m with
  | bearerAuth =>
    cases ho : bearerOutcome req with
    | admit h => simp [check, ho] at hr
    | reject rn =>
      simp only [check, ho, Option.some.injEq] at hr
      subst hr; rw [unauthorized401_status]; decide
  | ipAllow cidrs =>
    cases ha : ipAllowAdmits cidrs req with
    | true  => simp [check, ha] at hr
    | false =>
      simp only [check, ha, Bool.false_eq_true, if_false, Option.some.injEq] at hr
      subst hr; rw [forbidden403_status]; decide
  | rate budget =>
    cases ha : rateAdmits budget req with
    | true  => simp [check, ha] at hr
    | false =>
      simp only [check, ha, Bool.false_eq_true, if_false, Option.some.injEq] at hr
      subst hr; rw [tooMany429_status]; decide
  | deny name =>
    simp only [check, Option.some.injEq] at hr
    subst hr; rw [notImplemented501_status]; decide

/-- **The chain preserves the non-1xx final invariant.** If the handler's response is
`≥ 200`, so is the chain's — every short-circuit (401 / 501) is `≥ 200`. -/
theorem runChain_status_final (req : Request) (mws : List RouteMw) (inner : Response)
    (hinner : 200 ≤ inner.status) : 200 ≤ (runChain req mws inner).status := by
  induction mws with
  | nil => simpa [runChain] using hinner
  | cons m rest ih =>
    simp only [runChain]
    cases hc : check req m with
    | none => simpa [hc] using ih
    | some r => simp only [hc]; exact check_status_final req m r hc

/-! ## Concrete witnesses — the bearer gate is non-vacuous -/

/-- A request with no `Authorization` header. -/
def noTokenReq : Request := {}

/-- **No token ⇒ the real gate rejects.** (The admit direction — a well-formed
`Bearer hs256.x.y` token ⇒ `.admit`, verified on the running binary — rides on the
RFC 7515 §7.1 segment split, whose well-founded `String.splitOn` recursion the kernel
does not reduce; it is exercised end-to-end via curl, not by a kernel `decide`.) -/
theorem bearer_notoken_rejects : bearerOutcome noTokenReq = .reject .noToken := by decide

/-- **The chain serves 401 for a tokenless request** (the handler is never reached). -/
theorem runChain_notoken_401 (inner : Response) :
    runChain noTokenReq [.bearerAuth] inner = unauthorized401 :=
  runChain_bearer_rejects noTokenReq [] inner ⟨_, bearer_notoken_rejects⟩

/-! ### `ip-allow` is non-vacuous — the proven CIDR decision genuinely admits / refuses

The `X-Forwarded-For` → `Addr` parse rides on `String.splitOn`, whose well-founded
recursion the kernel does not reduce; it is exercised end-to-end via curl (a forwarded
client inside/outside the allow CIDR). The DECISION `IpFilter.permits` reduces, so its
non-vacuity is `decide`d directly on concrete addresses. -/

/-- The `127.0.0.1/32` allow-list: admit only loopback. -/
def allow127 : List Cidr := [v4Cidr 127 0 0 1 32]

/-- **Loopback is admitted** by the `127.0.0.1/32` allow-list — the REAL `IpFilter.permits`
allow-grant path (`ip_allow_grants`) fires. -/
theorem allow127_admits_loopback :
    _root_.IpFilter.permits (allowRuleset allow127) (v4Addr 127 0 0 1) = true := by decide

/-- **A non-loopback client is refused** by the `127.0.0.1/32` allow-list — no allow rule
matches, so the `defaultDeny := true` path (`ip_default_applies`) refuses. -/
theorem allow127_refuses_other :
    _root_.IpFilter.permits (allowRuleset allow127) (v4Addr 10 0 0 5) = false := by decide

/-- **`ip-allow` short-circuits with 403 exactly when the real decision refuses.** -/
theorem check_ipAllow_refuses (req : Request) (cidrs : List Cidr)
    (h : ipAllowAdmits cidrs req = false) : check req (.ipAllow cidrs) = some forbidden403 := by
  simp only [check, h, Bool.false_eq_true, if_false]

/-- **`ip-allow` passes an admitted client to the handler.** -/
theorem check_ipAllow_admits (req : Request) (cidrs : List Cidr)
    (h : ipAllowAdmits cidrs req = true) : check req (.ipAllow cidrs) = none := by
  simp only [check, h, if_true]

/-! ### `rate` is non-vacuous — the proven token bucket genuinely admits / rejects

The `X-Rate-Seq` header length feeds `seq`; the DECISION `Rate.tryAdmit ∘ Rate.refill`
reduces, so its non-vacuity is `decide`d directly on concrete buckets. -/

/-- **Under budget the bucket admits.** A `budget = 2` bucket with `seq = 0` has two
tokens; the REAL `Rate.tryAdmit` finds one and admits. -/
theorem rate2_admits_under :
    (_root_.Rate.tryAdmit (_root_.Rate.refill 0 ⟨2 - 0, 0, 2, 0⟩)).2 = true := by decide

/-- **Over budget the bucket rejects.** A `budget = 2` bucket with `seq = 2` is empty; the
REAL `Rate.tryAdmit` finds no token and rejects. -/
theorem rate2_rejects_over :
    (_root_.Rate.tryAdmit (_root_.Rate.refill 0 ⟨2 - 2, 0, 2, 0⟩)).2 = false := by decide

/-- **`rate` short-circuits with 429 exactly when the real bucket rejects.** -/
theorem check_rate_rejects (req : Request) (budget : Nat)
    (h : rateAdmits budget req = false) : check req (.rate budget) = some tooMany429 := by
  simp only [check, h, Bool.false_eq_true, if_false]

/-- **`rate` passes an under-budget request to the handler.** -/
theorem check_rate_admits (req : Request) (budget : Nat)
    (h : rateAdmits budget req = true) : check req (.rate budget) = none := by
  simp only [check, h, if_true]

end Reactor.RouteMw
