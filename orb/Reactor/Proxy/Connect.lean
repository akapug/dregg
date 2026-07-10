import Proxy.Basic

/-!
# Reactor.Proxy.Connect — the CONNECT-tunnel admission gate (default-deny) + blind relay

The HTTP `CONNECT` method asks the edge to open a bidirectional TCP tunnel to a
named `host:port` target and thereafter blindly forward bytes in both directions
(RFC 9110 §9.3.6). The dangerous part is *which* targets the edge will tunnel to:
"There are significant risks in establishing a tunnel to arbitrary servers …
Proxies that support CONNECT SHOULD restrict its use to a limited set of known
ports or a configurable list of safe request targets."

This module is the enforcement surface for that recommendation, split the same
way every other reactor decision is: the CORE decides *whether* a target is
admissible (a pure, proven predicate over an access-control list); the HOST owns
the socket and runs the byte pump once the core says `tunnel`.

## The gate

An `Acl` is `(allow, deny, defaultAllow)`. Admission (`Acl.check`) evaluates in a
fixed order that makes **deny authoritative** and the stance **default-deny**:

  1. **deny wins** — if any deny pattern matches the target, refuse (even if an
     allow pattern would also match, even if `defaultAllow`);
  2. **allow must match** — if the allow list is non-empty, admit iff at least
     one allow pattern matches;
  3. **fallthrough** — an empty allow list falls through to `defaultAllow`.

The canonical `Acl.denyAll` (`allow = deny = []`, `defaultAllow = false`) refuses
every target: an unconfigured edge tunnels to nothing.

## The relay

Once admitted the tunnel is a blind bidirectional pump. `Tunnel` tracks whether
the tunnel is `connected` plus the bytes delivered each way. The two guarantees:
no bytes cross before the tunnel is connected (`gated_no_relay_*`), and once
connected the relay is byte-faithful in both directions (`open_relay_faithful_*`)
— exactly RFC 9110's "blind forwarding of data, in both directions".

## Key theorems

* `deny_wins` — a target matching any deny pattern is refused unconditionally.
* `denyAll_refuses` / `default_deny` — the default ACL admits nothing; a target
  absent from a non-empty allow list (no deny match) is refused.
* `allow_admits` — a target matching an allow pattern (no deny match) is admitted.
* `decide_refused_iff` — `decide` opens a tunnel exactly when `check` holds, and
  refuses with `403` otherwise (a refusal never carries a tunnel).
* `gated_no_relay_up` / `gated_no_relay_down` — no byte escapes a gated tunnel.
* `open_relay_faithful_up` / `open_relay_faithful_down` — a connected tunnel
  relays exactly the input bytes, each direction.

## Boundaries

* Target *parsing* (splitting the request-line `host:port`) is a boundary; the
  byte-level export (`drorb_connect_gate`) does the split, the theorems speak
  over structured `Target`s. Host matching is exact-string / wildcard (glob and
  CIDR are a config-surface extension, not load-bearing here). The transport
  (DNS, TCP handshake) is the host's; the relay is modeled as byte lists.
-/

namespace Reactor.Proxy.Connect

/-- A CONNECT destination: host and TCP port. -/
structure Target where
  host : String
  port : Nat
deriving DecidableEq, Repr

/-- An ACL match pattern. `host = none` matches any host; `port = none` matches
any port. Both `none` is the catch-all pattern. -/
structure Pattern where
  host : Option String
  port : Option Nat
deriving DecidableEq, Repr

/-- Does a pattern match a target? Each axis matches iff it is a wildcard
(`none`) or equals the target's value. -/
def Pattern.matches (p : Pattern) (t : Target) : Bool :=
  (match p.host with | none => true | some h => h == t.host) &&
  (match p.port with | none => true | some q => q == t.port)

/-- An access-control list for CONNECT: an allow list, a deny list, and the
fallthrough stance for an empty allow list. -/
structure Acl where
  allow : List Pattern
  deny : List Pattern
  defaultAllow : Bool
deriving Repr

/-- The admission decision. Deny is authoritative; a non-empty allow list is
must-match-one; an empty allow list falls through to `defaultAllow`. -/
def Acl.check (a : Acl) (t : Target) : Bool :=
  if a.deny.any (·.matches t) then false
  else if a.allow.isEmpty then a.defaultAllow
  else a.allow.any (·.matches t)

/-- The default ACL: no allow, no deny, deny-by-default. Admits nothing. -/
def Acl.denyAll : Acl := { allow := [], deny := [], defaultAllow := false }

/-- An HTTPS-only ACL: admit any host on port 443, nothing else. -/
def Acl.httpsOnly : Acl :=
  { allow := [{ host := none, port := some 443 }], deny := [], defaultAllow := false }

/-- The gate verdict: open a tunnel to the target, or refuse with a status. -/
inductive Verdict where
  | tunnel (t : Target)
  | refused (status : Nat)
deriving DecidableEq, Repr

/-- The CONNECT decision: tunnel iff the ACL admits, else refuse `403`. -/
def decide (a : Acl) (t : Target) : Verdict :=
  if a.check t then .tunnel t else .refused 403

/-! ## Gate theorems -/

/-- **Deny is authoritative.** A target matching any deny pattern is refused,
regardless of the allow list or `defaultAllow`. -/
theorem deny_wins {a : Acl} {t : Target} (h : a.deny.any (·.matches t) = true) :
    a.check t = false := by
  simp only [Acl.check, h, if_true]

/-- A denied target never opens a tunnel. -/
theorem deny_no_tunnel {a : Acl} {t : Target}
    (h : a.deny.any (·.matches t) = true) : ∀ t', decide a t ≠ .tunnel t' := by
  intro t'
  simp only [decide, deny_wins h, if_false]
  exact fun h => nomatch h

/-- **Default deny.** The canonical ACL refuses every target. -/
theorem denyAll_refuses (t : Target) : Acl.denyAll.check t = false := by
  simp [Acl.check, Acl.denyAll]

/-- **Default deny, decision level.** The default ACL always yields `refused 403`. -/
theorem denyAll_decide (t : Target) : decide Acl.denyAll t = .refused 403 := by
  simp [decide, denyAll_refuses]

/-- **Allow-list default-deny.** With a non-empty allow list and no deny match, a
target that matches *no* allow pattern is refused: the allow list is itself a
default-deny surface, not an addendum to a permissive base. -/
theorem allow_must_match {a : Acl} {t : Target}
    (hne : a.allow.isEmpty = false)
    (hdeny : a.deny.any (·.matches t) = false)
    (hallow : a.allow.any (·.matches t) = false) :
    a.check t = false := by
  simp [Acl.check, hdeny, hne, hallow]

/-- **Allow admits.** A target matching an allow pattern (and no deny pattern) is
admitted. -/
theorem allow_admits {a : Acl} {t : Target}
    (hdeny : a.deny.any (·.matches t) = false)
    (hallow : a.allow.any (·.matches t) = true) :
    a.check t = true := by
  have hne : a.allow.isEmpty = false := by
    cases hlist : a.allow with
    | nil => rw [hlist] at hallow; simp at hallow
    | cons _ _ => rfl
  simp [Acl.check, hdeny, hne, hallow]

/-- **`decide` tracks `check` exactly**: it opens a tunnel iff admission holds,
and a refusal always carries `403` and never a tunnel. -/
theorem decide_refused_iff {a : Acl} {t : Target} :
    decide a t = .refused 403 ↔ a.check t = false := by
  unfold decide
  cases h : a.check t <;> simp [h]

theorem decide_tunnel_iff {a : Acl} {t : Target} :
    decide a t = .tunnel t ↔ a.check t = true := by
  unfold decide
  cases h : a.check t <;> simp [h]

/-! ## Non-vacuity: concrete admit/deny -/

/-- A disallowed target under the default ACL: refused `403`. -/
example : decide Acl.denyAll { host := "evil.example", port := 22 } = .refused 403 := rfl

/-- An HTTPS target under `httpsOnly`: the tunnel opens. -/
example : decide Acl.httpsOnly { host := "api.internal", port := 443 }
    = .tunnel { host := "api.internal", port := 443 } := rfl

/-- A non-443 target under `httpsOnly`: refused (allow-list default-deny). -/
example : decide Acl.httpsOnly { host := "api.internal", port := 22 } = .refused 403 := rfl

/-- Deny beats allow: a target on both lists is refused. -/
example :
    let a : Acl := { allow := [{ host := none, port := none }],
                     deny := [{ host := some "blocked.example", port := none }],
                     defaultAllow := true }
    decide a { host := "blocked.example", port := 443 } = .refused 403 := rfl

/-! ## The blind bidirectional relay -/

/-- A CONNECT tunnel: whether it is connected, and the bytes delivered each way
(`c2u` client→upstream, `u2c` upstream→client). -/
structure Tunnel where
  connected : Bool
  c2u : List UInt8
  u2c : List UInt8
deriving DecidableEq, Repr

/-- A freshly admitted-but-not-yet-connected tunnel: gated, no bytes. -/
def Tunnel.gated : Tunnel := { connected := false, c2u := [], u2c := [] }

/-- Open the tunnel (the host reports the upstream TCP connect succeeded). -/
def Tunnel.opened : Tunnel := { connected := true, c2u := [], u2c := [] }

/-- Pump client→upstream bytes: appended iff connected, dropped otherwise. -/
def Tunnel.pumpUp (tun : Tunnel) (b : List UInt8) : Tunnel :=
  if tun.connected then { tun with c2u := tun.c2u ++ b } else tun

/-- Pump upstream→client bytes: appended iff connected, dropped otherwise. -/
def Tunnel.pumpDown (tun : Tunnel) (b : List UInt8) : Tunnel :=
  if tun.connected then { tun with u2c := tun.u2c ++ b } else tun

/-- **No relay before connect (up).** A gated tunnel drops client bytes. -/
theorem gated_no_relay_up (b : List UInt8) :
    (Tunnel.gated.pumpUp b).c2u = [] := by
  simp [Tunnel.pumpUp, Tunnel.gated]

/-- **No relay before connect (down).** A gated tunnel drops upstream bytes. -/
theorem gated_no_relay_down (b : List UInt8) :
    (Tunnel.gated.pumpDown b).u2c = [] := by
  simp [Tunnel.pumpDown, Tunnel.gated]

/-- **Faithful blind relay (up).** A connected tunnel delivers exactly the
client bytes upstream. -/
theorem open_relay_faithful_up (b : List UInt8) :
    (Tunnel.opened.pumpUp b).c2u = b := by
  simp [Tunnel.pumpUp, Tunnel.opened]

/-- **Faithful blind relay (down).** A connected tunnel delivers exactly the
upstream bytes to the client. -/
theorem open_relay_faithful_down (b : List UInt8) :
    (Tunnel.opened.pumpDown b).u2c = b := by
  simp [Tunnel.pumpDown, Tunnel.opened]

/-! ## The byte-level host seam -/

/-- Parse a `host:port` target from a line (split on the final colon). `none` on
a missing/non-numeric port. -/
def parseTarget (s : String) : Option Target :=
  match s.splitOn ":" with
  | [h, p] => (p.toNat?).map (fun n => { host := h, port := n })
  | _ => none

/-- Parse an allow-list pattern from a `host:port` line. `*` on either axis is a
wildcard. A malformed line becomes the catch-nothing pattern. -/
def parsePattern (s : String) : Pattern :=
  match s.splitOn ":" with
  | [h, p] =>
    { host := if h == "*" then none else some h,
      port := if p == "*" then none else p.toNat? }
  | _ => { host := some s, port := some 0 }

/-- **The proven CONNECT gate, byte seam.** Input is UTF-8, newline-separated:
line 0 is the `host:port` target, the remaining lines are the allow-list
patterns (`*` = wildcard). The stance is default-deny (empty deny list,
`defaultAllow = false`), so the host contributes only the configured allow
patterns and the parsed target — never the decision. Output is a single byte:
`1` ⇒ open the tunnel, `0` ⇒ refuse `403`. -/
@[export drorb_connect_gate]
def connectGate (input : ByteArray) : ByteArray :=
  let s := (String.fromUTF8? input).getD ""
  let lines := (s.splitOn "\n").filter (· ≠ "")
  match lines with
  | [] => ByteArray.mk #[0]
  | target :: allowLines =>
    match parseTarget target with
    | none => ByteArray.mk #[0]
    | some t =>
      let a : Acl := { allow := allowLines.map parsePattern, deny := [], defaultAllow := false }
      match decide a t with
      | .tunnel _ => ByteArray.mk #[1]
      | .refused _ => ByteArray.mk #[0]

/-- The byte seam refuses an unparseable target line. -/
example : (connectGate (String.toUTF8 "not-a-target")).toList = [0] := by native_decide

/-- The byte seam opens a tunnel for an allowed target. -/
example : (connectGate (String.toUTF8 "api.internal:443\n*:443")).toList = [1] := by native_decide

/-- The byte seam refuses a target absent from the allow list. -/
example : (connectGate (String.toUTF8 "api.internal:22\n*:443")).toList = [0] := by native_decide

end Reactor.Proxy.Connect
