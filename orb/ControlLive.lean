/-
# ControlLive — driving the PROVEN ts2021 control plane over the byte level

The `Control` foundation and `Control.Channel` model the coordination server
("control plane") of a mesh VPN as sans-IO, proven Lean: the ts2021 Noise-IK
handshake as a transition system (`Control.Channel.step` to `.up`, keys agreeing
via `handshake_keys_agree`), the AEAD-sealed control frame carrying every wire
message (`seal_open` and the `{regReq,mapReq,regResp,mapResp}_channel_roundtrip`
lemmas), the server transition system (`Control.step`: register → authorize →
mapPoll → netmap), the netmap delta fold (`NetMap.applyDelta`), MagicDNS
resolution (`DnsConfig.resolve`), and cryptokey-routing translation
(`NetMap.toWgPeers`).

None of that logic was wired into a running binary. This executable is that
wiring: a `selftest` that drives BOTH ends — a **coord** (responder) and a
**node** (initiator) — over the byte level in one process (no sockets yet), so
the whole PROVEN pipeline is EXERCISED end to end:

  1. both ends drive `Control.Channel.step` to `.up` — the Noise-IK handshake,
     transport keys agreeing (the runtime cross-check confirms what
     `handshake_keys_agree` proves: node.send == coord.recv, node.recv ==
     coord.send);
  2. the node builds + seals a `RegisterRequest` under its send key; the coord
     opens it under the matching receive key and runs `Control.step .register`,
     authorizing the machine under a `Policy`;
  3. the node seals a `MapRequest`; the coord opens it and runs
     `Control.step .mapPoll`, replying with a sealed `MapResponse.full` carrying
     the authorized-peer netmap;
  4. the node opens the response (`openMapResp`), folds `NetMap.applyDelta`,
     resolves a MagicDNS name (`DnsConfig.resolve`), and programs the WireGuard
     peer table (`NetMap.toWgPeers`);
  5. it prints the resulting WG peers + DNS result and a PASS/FAIL cross-check
     against the model decision — the realization of
     `control_applies_netmap_faithfully`.

## Honesty / realization boundary (the DiscoLive discipline)

This is **drorb-native**: both ends are our own spec-conformant control-plane
peers speaking the modelled ts2021 wire format — NOT real Tailscale / headscale
interop, which additionally needs the byte-exact `controlbase` header offsets
and a tailnet auth key (operator-provided; the named residual in
`Control/Channel.lean §7`). Like DiscoLive / wg-live this is a live cross-check,
not part of the trusted core: everything cryptographic/structural is the proven
Lean. The gap the selftest discharges (by construction, not by proof) is that
this exe faithfully CALLS the proven Lean functions on real bytes; the
faithfulness of the decode→apply chain ITSELF is proven below as
`control_applies_netmap_faithfully`.

Usage:
  control-live selftest
-/
import Control.Channel

namespace ControlLive

open Control
open Control.Channel (bytesOf baOf nonce0)

/-! ## The Phase-0 faithfulness theorem

The running loop's decode→apply chain applies EXACTLY the proven decision. Given
the coord's decided `MapResponse m` sealed into a frame under its send key, the
node's `openMapResp` (= parseFrame → chachaOpen → getMapResp) followed by the
netmap fold (`applyDelta`) and cryptokey-routing translation (`toWgPeers`)
produces PRECISELY what the model computes by folding the SAME decision `m` — the
bytes on the wire realize the model, mediated only by the proven round-trips
(`frame_roundtrip`, `seal_open`, `getMapResp_put`, chained by
`mapResp_channel_roundtrip`). Not a `P → P`: it is inhabited (the selftest below
produces such a `frame`) and its content is the crypto+codec round-trip. -/
theorem control_applies_netmap_faithfully
    (sk rk nonce : ByteArray) (nm0 : NetMap) (m : MapResponse)
    (hk : sk = rk) {frame : Control.Bytes}
    (hs : Control.Channel.sealMapResp sk nonce m = some frame) :
    (Control.Channel.openMapResp rk nonce frame).map
        (fun r => (nm0.applyDelta r).toWgPeers)
      = some (nm0.applyDelta m).toWgPeers := by
  rw [Control.Channel.mapResp_channel_roundtrip sk rk nonce m hk hs]
  rfl

#print axioms control_applies_netmap_faithfully

/-! ## Phase-1 : the live handshake refines the proven FSM

Phase 0 drove `Control.Channel.step` over the byte level in one process. Phase 1
splits into two OS processes over a real TCP socket: a **coord** that
listens/accepts and a **node** that connects. The socket driver (below) feeds
`Control.Channel.step` exactly the public-key bytes that traversed the wire — the
node's ephemeral+machine-static in the initiation, the coord's ephemeral in the
response. This theorem is the refinement obligation the two-process run
discharges: *whatever* well-formed key bytes the socket carried, driving the FSM
with them lands **both** ends in `.up` with **agreeing** transport keys
(`node.send == coord.recv ∧ node.recv == coord.send`) — the runtime realization
of `handshake_keys_agree` composed with `tx_directions_agree`.

It is the FSM-level (`Control.Channel.step`) statement, not just the material
function: the coord's `step … (.recvInit nodeEph nodeStatic)` and the node's
`step … (.recvResp coordEph)` are the exact transitions the socket loop invokes.
Non-vacuous: the hypotheses are the satisfiable well-formedness of the keypairs
(the selftest/live keys satisfy them) and that the node's Noise material exists;
the conclusion is a concrete equality about `step`'s output, not a tautology.

Realization boundary (named): the socket driver realizes the model by *calling*
`step` on the bytes `recv`/`send` moved; that the C shim faithfully moves those
bytes is discharged by construction (the live 2-process run), exactly as
`control_applies_netmap_faithfully` handles the decode→apply chain. -/
open Control.Channel in
theorem control_handshake_refines
    (nodeSess coordSess : Session) (m : ByteArray)
    (hPeerS : nodeSess.peerS = coordSess.spub)
    (hM  : Crypto.x25519Base nodeSess.spriv = some nodeSess.spub)
    (hE  : Crypto.x25519Base nodeSess.epriv = some nodeSess.epub)
    (hS  : Crypto.x25519Base coordSess.spriv = some coordSess.spub)
    (hES : Crypto.x25519Base coordSess.epriv = some coordSess.epub)
    (hNode : nodeMaterial nodeSess.spriv nodeSess.epriv nodeSess.epub
               nodeSess.peerS coordSess.epub = some m) :
    ∃ nodeTx coordTx,
      step coordSess Phase.fresh (Ev.recvInit nodeSess.epub nodeSess.spub)
        = (Phase.up coordTx, Out.sendResp coordSess.epub) ∧
      step nodeSess Phase.awaitResp (Ev.recvResp coordSess.epub)
        = (Phase.up nodeTx, Out.idle) ∧
      nodeTx.send = coordTx.recv ∧ nodeTx.recv = coordTx.send := by
  obtain ⟨hServer, hd1, hd2⟩ :=
    channel_established_keys_agree
      nodeSess.spriv nodeSess.epriv coordSess.spriv coordSess.epriv
      nodeSess.spub nodeSess.epub coordSess.spub coordSess.epub m
      hM hE hS hES (hPeerS ▸ hNode)
  exact ⟨initiatorTx m, responderTx m,
    by simp only [Control.Channel.step, hServer],
    by simp only [Control.Channel.step, hNode], hd1, hd2⟩

#print axioms control_handshake_refines

/-! ## The untrusted TCP socket seam

The client half (connect/send/recvExact/close) is reused from `ffi/derp_net.c`
(the same shim `derp-live` uses); the server half (listen/accept) is
`ffi/control_net.c`, the only server capability derp_net.c lacks. These are the
untrusted environment — they move bytes and hold no protocol state. -/

@[extern "drorb_tcp_connect"]
opaque tcpConnect (host : String) (port : UInt16) : IO UInt32
@[extern "drorb_tcp_send"]
opaque tcpSend (fd : UInt32) (payload : ByteArray) : IO Unit
@[extern "drorb_tcp_recv_exact"]
opaque tcpRecvExact (fd : UInt32) (nbytes : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)
@[extern "drorb_tcp_close"]
opaque tcpClose (fd : UInt32) : IO Unit
@[extern "drorb_tcp_listen"]
opaque tcpListen (port : UInt16) : IO UInt32
@[extern "drorb_tcp_accept"]
opaque tcpAccept (lfd : UInt32) (timeoutMs : UInt32) : IO (Option UInt32)

/-! ## Byte helpers (mirrors DiscoLive/DerpLive) -/

def ofHex (s : String) : ByteArray := Id.run do
  let cs := s.toList.filter (fun c => c ≠ ' ' ∧ c ≠ '\n')
  let hexVal : Char → Option UInt8 := fun c =>
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
    else none
  let rec go : List Char → ByteArray → ByteArray
    | hi :: lo :: rest, acc =>
      match hexVal hi, hexVal lo with
      | some h, some l => go rest (acc.push (h * 16 + l))
      | _, _ => acc
    | _, acc => acc
  go cs (ByteArray.mk #[])

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def toHexL (b : Control.Bytes) : String := toHex (baOf b)

/-- Render a byte list that is UTF-8 text as text (for names), else hex. -/
def textOrHex (b : Control.Bytes) : String := (String.fromUTF8? (baOf b)).getD (toHexL b)

/-- A fixed 32-byte placeholder key value. -/
def dummyKey (v : UInt8) : Control.Bytes := List.replicate 32 v

/-! ## The selftest — both ends over the byte level -/

def selftest : IO UInt32 := do
  IO.println "== control-live selftest : ts2021 Noise-IK control plane, byte-level, both ends =="

  -- Key material (curve25519 scalars; clamping handled inside x25519).
  let mpriv   := ofHex "a01111111111111111111111111111111111111111111111111111111111111a"  -- node machine static
  let nEpriv  := ofHex "c03333333333333333333333333333333333333333333333333333333333333c"  -- node ephemeral
  let sPriv   := ofHex "b02222222222222222222222222222222222222222222222222222222222222b"  -- coord server static
  let sEpriv  := ofHex "d04444444444444444444444444444444444444444444444444444444444444d"  -- coord ephemeral
  let noKPriv := ofHex "e05555555555555555555555555555555555555555555555555555555555555e"  -- node overlay node-key
  let dsKPriv := ofHex "f06666666666666666666666666666666666666666666666666666666666666f"  -- node disco key

  let some mpub  := Crypto.x25519Base mpriv  | do IO.eprintln "x25519Base(machine) failed"; return 1
  let some nEpub := Crypto.x25519Base nEpriv | do IO.eprintln "x25519Base(node eph) failed"; return 1
  let some sPub  := Crypto.x25519Base sPriv  | do IO.eprintln "x25519Base(server static) failed"; return 1
  let some sEpub := Crypto.x25519Base sEpriv | do IO.eprintln "x25519Base(server eph) failed"; return 1
  let some nkPub := Crypto.x25519Base noKPriv | do IO.eprintln "x25519Base(node key) failed"; return 1
  let some dsPub := Crypto.x25519Base dsKPriv | do IO.eprintln "x25519Base(disco key) failed"; return 1

  let nodeOverlayKey : NodeKey := ⟨bytesOf nkPub⟩
  let nodeDiscoKey   : DiscoKey := ⟨bytesOf dsPub⟩
  let nodeMachineKey : MachineKey := ⟨bytesOf mpub⟩

  IO.println s!"node machine  pub : {toHex mpub}"
  IO.println s!"node overlay  key : {toHex nkPub}"
  IO.println s!"coord server  pub : {toHex sPub}"

  -- ── 1. the Noise-IK handshake, both ends, driven through the PROVEN FSM ──
  let nodeSess : Control.Channel.Session :=
    { role := .node, spriv := mpriv, spub := mpub, epriv := nEpriv, epub := nEpub, peerS := sPub }
  let coordSess : Control.Channel.Session :=
    { role := .coord, spriv := sPriv, spub := sPub, epriv := sEpriv, epub := sEpub, peerS := ByteArray.empty }

  let (nodeP1, _o1) := Control.Channel.step nodeSess .fresh .start           -- node: fresh --start--> awaitResp
  let (coordP, _oc) := Control.Channel.step coordSess .fresh (.recvInit nEpub mpub)  -- coord: fresh --recvInit--> up
  let (nodeP,  _on) := Control.Channel.step nodeSess nodeP1 (.recvResp sEpub)        -- node: awaitResp --recvResp--> up

  let some coordTx := (match coordP with | .up tx => some tx | _ => none)
    | do IO.eprintln "coord did not reach .up"; return 1
  let some nodeTx := (match nodeP with | .up tx => some tx | _ => none)
    | do IO.eprintln "node did not reach .up"; return 1

  let keysAgree :=
    (nodeTx.send.toList == coordTx.recv.toList) && (nodeTx.recv.toList == coordTx.send.toList)
  IO.println "\n-- handshake --"
  IO.println s!"node  send key : {toHex nodeTx.send}"
  IO.println s!"coord recv key : {toHex coordTx.recv}"
  IO.println s!"transport keys agree (node.send==coord.recv ∧ node.recv==coord.send) : {keysAgree}"
  if !keysAgree then do IO.eprintln "handshake keys did NOT agree"; return 1
  IO.println "handshake UP (Noise-IK, `handshake_keys_agree` realized on real crypto)."

  -- ── the coordination server's world: one already-authorized peer to hand down ──
  let peerNode : Node :=
    { id := 42, stableID := "peer-stable-id".toUTF8.toList,
      name := "peer.example.ts.net".toUTF8.toList, user := 1,
      key := ⟨dummyKey 0xab⟩, machine := ⟨dummyKey 0xcd⟩, disco := ⟨dummyKey 0xef⟩,
      addresses  := [{ addr := [100,64,0,2], bits := 32 }],
      allowedIPs := [{ addr := [100,64,0,2], bits := 32 }, { addr := [10,0,0,0], bits := 24 }],
      endpoints  := [{ addr := [192,168,1,50], port := 41641 }],
      derp := 1, online := true, keyExpiry := 0, authorized := true }
  let peerReg : Registration := { nodeKey := peerNode.key, node := peerNode, status := .authorized }
  let serverDns : DnsConfig :=
    { domains := ["example.ts.net".toUTF8.toList],
      records := [(peerNode.name, [100,64,0,2])] }
  let serverFilter : PacketFilter :=
    [{ srcIPs := [{ addr := [100,64,0,0], bits := 10 }],
       dstPorts := [{ net := { addr := [100,64,0,0], bits := 10 }, ports := { first := 0, last := 65535 } }],
       protos := [] }]
  let s0 : ControlState := { nodes := [peerReg], filter := serverFilter, dns := serverDns }
  let pol : Policy := { authorizes := fun _ _ => true }

  -- ── 2. node → RegisterRequest, sealed; coord opens + Control.step .register ──
  let regReq : RegisterRequest :=
    { version := 1, nodeKey := nodeOverlayKey, oldNodeKey := ⟨[]⟩, machineKey := nodeMachineKey,
      authKey := "tskey-auth-selftest".toUTF8.toList, expiry := 0, ephemeral := false, followup := false }
  let some regFrame := Control.Channel.sealRegReq nodeTx.send nonce0 regReq
    | do IO.eprintln "sealRegReq failed"; return 1
  let some regReq' := Control.Channel.openRegReq coordTx.recv nonce0 regFrame
    | do IO.eprintln "coord could not open RegisterRequest"; return 1
  let regOk := regReq' == regReq
  IO.println "\n-- register --"
  IO.println s!"node -> RegisterRequest frame ({(baOf regFrame).size}B), coord opened it, decoded == sent : {regOk}"
  if !regOk then do IO.eprintln "RegisterRequest did not round-trip"; return 1
  let (s1, regReply) := Control.step pol s0 (.register regReq')
  let regAuthorized :=
    match regReply with | .registerResp r => r.machineAuthorized | _ => false
  IO.println s!"coord Control.step .register -> machineAuthorized : {regAuthorized}"
  if !regAuthorized then do IO.eprintln "node was not authorized"; return 1

  -- ── 3. node → MapRequest, sealed; coord opens + Control.step .mapPoll ──
  let mapReq : MapRequest :=
    { version := 1, nodeKey := nodeOverlayKey, discoKey := nodeDiscoKey,
      endpoints := [{ addr := [192,168,1,10], port := 41641 }],
      stream := true, omitPeers := false, readOnly := false }
  let some mapFrame := Control.Channel.sealMapReq nodeTx.send nonce0 mapReq
    | do IO.eprintln "sealMapReq failed"; return 1
  let some mapReq' := Control.Channel.openMapReq coordTx.recv nonce0 mapFrame
    | do IO.eprintln "coord could not open MapRequest"; return 1
  let mapOk := mapReq' == mapReq
  IO.println "\n-- map poll --"
  IO.println s!"node -> MapRequest frame ({(baOf mapFrame).size}B), coord opened it, decoded == sent : {mapOk}"
  if !mapOk then do IO.eprintln "MapRequest did not round-trip"; return 1
  let (_s2, mapReply) := Control.step pol s1 (.mapPoll mapReq')
  let some mresp := (match mapReply with | .mapResp m => some m | _ => none)
    | do IO.eprintln "coord REJECTED the poll (node not authorized?)"; return 1

  -- ── 4. coord seals MapResponse; node opens, folds, resolves DNS, programs WG ──
  let some respFrame := Control.Channel.sealMapResp coordTx.send nonce0 mresp
    | do IO.eprintln "sealMapResp failed"; return 1
  let some mresp' := Control.Channel.openMapResp nodeTx.recv nonce0 respFrame
    | do IO.eprintln "node could not open MapResponse"; return 1

  -- the node's current (self-only) netmap, before folding the server's response
  let selfNode : Node :=
    { id := 0, stableID := [], name := "self.example.ts.net".toUTF8.toList, user := 1,
      key := nodeOverlayKey, machine := nodeMachineKey, disco := nodeDiscoKey,
      addresses := [{ addr := [100,64,0,1], bits := 32 }], allowedIPs := [], endpoints := [],
      derp := 1, online := true, keyExpiry := 0, authorized := true }
  let nm0 : NetMap := { self := selfNode, peers := [], dns := DnsConfig.empty, packetFilter := [] }

  let nmApplied := nm0.applyDelta mresp'          -- fold the decoded response
  let wgPeers   := nmApplied.toWgPeers            -- program the WireGuard peer table
  let dnsResult := nmApplied.dns.resolve peerNode.name  -- MagicDNS resolution over the netmap DNS

  IO.println s!"\n-- netmap applied (coord -> node, {(baOf respFrame).size}B sealed frame) --"
  IO.println s!"peers in netmap        : {nmApplied.peers.length}"
  IO.println s!"packet-filter rules    : {nmApplied.packetFilter.length}"
  for p in wgPeers do
    let cidrs := p.allowed.map (fun c => s!"{c.addr}/{c.plen}")
    IO.println s!"  WG peer  spub={toHex p.spub}  allowedIPs={cidrs}"
  match dnsResult with
  | some addr => IO.println s!"MagicDNS resolve       : {textOrHex peerNode.name} -> {addr}"
  | none      => IO.println s!"MagicDNS resolve       : {textOrHex peerNode.name} -> (no record)"

  -- ── 5. the faithfulness cross-check: wire decode∘fold∘toWgPeers == model decision ──
  -- `control_applies_netmap_faithfully` PROVES these are equal for the sealed frame;
  -- here we witness it on the concrete bytes (spub key lists compared).
  let modelWg := (nm0.applyDelta mresp).toWgPeers
  let wireKeys  := wgPeers.map (fun p => p.spub.toList)
  let modelKeys := modelWg.map (fun p => p.spub.toList)
  let faithful := (wireKeys == modelKeys) && !wgPeers.isEmpty
  let dnsGood := dnsResult == some ([100,64,0,2] : Control.Bytes)

  IO.println "\n-- cross-check (realizes control_applies_netmap_faithfully) --"
  IO.println s!"wire WG peers == model WG peers : {wireKeys == modelKeys}"
  IO.println s!"WG peer table non-empty         : {!wgPeers.isEmpty}"
  IO.println s!"MagicDNS resolved as expected   : {dnsGood}"

  if keysAgree && regOk && regAuthorized && mapOk && faithful && dnsGood then do
    IO.println "\nPASS — handshake UP, node authorized, netmap applied, WG peers programmed;"
    IO.println "       the decode→apply→toWgPeers chain equals the proven model decision."
    IO.println "FULL CONTROL-PLANE EXCHANGE COMPLETE (drorb-native, byte-level, verified crypto+codec)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the control-plane pipeline did not cross-check."
    return 1

/-! ## Phase-1 : two REAL processes over TCP (coord + node)

The selftest above drove both ends over the byte level in ONE process. Here they
are split into two OS processes speaking over a real TCP socket. The socket
carries three things: a fixed-size handshake INIT (node ephemeral ‖ node machine
static), a fixed-size handshake RESP (coord ephemeral), and length-prefixed
sealed control frames. The `Control.Channel.step` FSM and the sealed-frame codecs
are the SAME proven functions the selftest used; only the transport changed. -/

def recvTimeout : UInt32 := 15000

/-- Big-endian 4-byte length prefix (untrusted socket framing, distinct from the
proven inner frame codec — the C-shim sibling of DerpLive's `be32`). -/
def be32enc (n : Nat) : ByteArray :=
  ByteArray.mk #[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]
def be32dec (b : ByteArray) : Nat :=
  (b.get! 0).toNat * 16777216 + (b.get! 1).toNat * 65536 + (b.get! 2).toNat * 256 + (b.get! 3).toNat

/-- Send a sealed control frame length-prefixed. -/
def sendFrame (fd : UInt32) (frame : Control.Bytes) : IO Unit := do
  let fb := baOf frame
  tcpSend fd (be32enc fb.size)
  tcpSend fd fb

/-- Read one length-prefixed sealed control frame off the stream. -/
def recvFrame (fd : UInt32) : IO (Option Control.Bytes) := do
  match ← tcpRecvExact fd 4 recvTimeout with
  | none => return none
  | some hb =>
    match ← tcpRecvExact fd (UInt32.ofNat (be32dec hb)) recvTimeout with
    | none => return none
    | some pb => return some (bytesOf pb)

/-- Shared fixed key material of this drorb-native test tailnet — the SAME
constants the selftest uses, so the two processes' Noise-IK handshake agrees. A
real tailnet supplies these per device out of band (the named residual). -/
structure Km where
  mpriv : ByteArray
  mpub : ByteArray
  nEpriv : ByteArray
  nEpub : ByteArray
  sPriv : ByteArray
  sPub : ByteArray
  sEpriv : ByteArray
  sEpub : ByteArray
  nkPub : ByteArray
  dsPub : ByteArray

def mkKeys : IO (Option Km) := do
  let mpriv   := ofHex "a01111111111111111111111111111111111111111111111111111111111111a"
  let nEpriv  := ofHex "c03333333333333333333333333333333333333333333333333333333333333c"
  let sPriv   := ofHex "b02222222222222222222222222222222222222222222222222222222222222b"
  let sEpriv  := ofHex "d04444444444444444444444444444444444444444444444444444444444444d"
  let noKPriv := ofHex "e05555555555555555555555555555555555555555555555555555555555555e"
  let dsKPriv := ofHex "f06666666666666666666666666666666666666666666666666666666666666f"
  match Crypto.x25519Base mpriv, Crypto.x25519Base nEpriv, Crypto.x25519Base sPriv,
        Crypto.x25519Base sEpriv, Crypto.x25519Base noKPriv, Crypto.x25519Base dsKPriv with
  | some mpub, some nEpub, some sPub, some sEpub, some nkPub, some dsPub =>
      return some { mpriv, mpub, nEpriv, nEpub, sPriv, sPub, sEpriv, sEpub, nkPub, dsPub }
  | _, _, _, _, _, _ => return none

/-- The coord's already-authorized peer + tailnet config (drorb-native world). -/
def coordState : ControlState :=
  let peerNode : Node :=
    { id := 42, stableID := "peer-stable-id".toUTF8.toList,
      name := "peer.example.ts.net".toUTF8.toList, user := 1,
      key := ⟨dummyKey 0xab⟩, machine := ⟨dummyKey 0xcd⟩, disco := ⟨dummyKey 0xef⟩,
      addresses  := [{ addr := [100,64,0,2], bits := 32 }],
      allowedIPs := [{ addr := [100,64,0,2], bits := 32 }, { addr := [10,0,0,0], bits := 24 }],
      endpoints  := [{ addr := [192,168,1,50], port := 41641 }],
      derp := 1, online := true, keyExpiry := 0, authorized := true }
  { nodes := [{ nodeKey := peerNode.key, node := peerNode, status := .authorized }],
    filter :=
      [{ srcIPs := [{ addr := [100,64,0,0], bits := 10 }],
         dstPorts := [{ net := { addr := [100,64,0,0], bits := 10 }, ports := { first := 0, last := 65535 } }],
         protos := [] }],
    dns := { domains := ["example.ts.net".toUTF8.toList],
             records := [(peerNode.name, [100,64,0,2])] } }

/-- COORD process: listen, accept a node, drive the responder handshake to `.up`
over the socket, then serve register + map-poll. -/
def coord (port : UInt16) : IO UInt32 := do
  IO.println s!"== control-live COORD : ts2021 responder, listening 127.0.0.1:{port} =="
  let some k ← mkKeys | do IO.eprintln "coord: key derivation failed"; return 1
  let lfd ← tcpListen port
  IO.println "coord: listening; waiting for a node to connect..."
  let some cfd ← tcpAccept lfd 60000 | do IO.eprintln "coord: accept timed out"; tcpClose lfd; return 1
  IO.println "coord: node connected (accepted a real TCP connection)."

  -- 1. read the handshake INIT (node ephemeral ‖ node machine static), drive step
  let some initb ← tcpRecvExact cfd 64 recvTimeout
    | do IO.eprintln "coord: no init frame"; tcpClose cfd; tcpClose lfd; return 1
  let nEpub := initb.extract 0 32
  let mpub  := initb.extract 32 64
  let coordSess : Control.Channel.Session :=
    { role := .coord, spriv := k.sPriv, spub := k.sPub, epriv := k.sEpriv, epub := k.sEpub,
      peerS := ByteArray.empty }
  let (coordP, out) := Control.Channel.step coordSess .fresh (.recvInit nEpub mpub)
  let some coordTx := (match coordP with | .up tx => some tx | _ => none)
    | do IO.eprintln "coord: handshake did not reach .up"; tcpClose cfd; tcpClose lfd; return 1
  match out with
  | .sendResp epub => tcpSend cfd epub
  | _ => do IO.eprintln "coord: no response to emit"; tcpClose cfd; tcpClose lfd; return 1
  IO.println s!"coord: handshake UP; recv key : {toHex coordTx.recv}"

  let pol : Policy := { authorizes := fun _ _ => true }
  -- 2. sealed RegisterRequest -> Control.step .register
  let some regFrame ← recvFrame cfd | do IO.eprintln "coord: no RegisterRequest"; tcpClose cfd; tcpClose lfd; return 1
  let some regReq' := Control.Channel.openRegReq coordTx.recv nonce0 regFrame
    | do IO.eprintln "coord: could not open RegisterRequest"; tcpClose cfd; tcpClose lfd; return 1
  let (s1, regReply) := Control.step pol coordState (.register regReq')
  let regAuthorized := match regReply with | .registerResp r => r.machineAuthorized | _ => false
  IO.println s!"coord: opened RegisterRequest, Control.step .register -> authorized : {regAuthorized}"
  -- 3. sealed MapRequest -> Control.step .mapPoll -> sealed MapResponse.full
  let some mapFrame ← recvFrame cfd | do IO.eprintln "coord: no MapRequest"; tcpClose cfd; tcpClose lfd; return 1
  let some mapReq' := Control.Channel.openMapReq coordTx.recv nonce0 mapFrame
    | do IO.eprintln "coord: could not open MapRequest"; tcpClose cfd; tcpClose lfd; return 1
  let (_s2, mapReply) := Control.step pol s1 (.mapPoll mapReq')
  let some mresp := (match mapReply with | .mapResp m => some m | _ => none)
    | do IO.eprintln "coord: rejected the poll"; tcpClose cfd; tcpClose lfd; return 1
  let some respFrame := Control.Channel.sealMapResp coordTx.send nonce0 mresp
    | do IO.eprintln "coord: sealMapResp failed"; tcpClose cfd; tcpClose lfd; return 1
  sendFrame cfd respFrame
  IO.println s!"coord: sealed MapResponse.full ({(baOf respFrame).size}B) delivered to node."
  tcpClose cfd; tcpClose lfd
  IO.println "coord: DONE (drorb-native responder, real TCP)."
  return 0

/-- NODE process: connect, drive the initiator handshake to `.up` over the
socket, register + poll, then apply the netmap and program the WG peers. -/
def node (host : String) (port : UInt16) : IO UInt32 := do
  IO.println s!"== control-live NODE : ts2021 initiator, connecting {host}:{port} =="
  let some k ← mkKeys | do IO.eprintln "node: key derivation failed"; return 1
  let nodeOverlayKey : NodeKey := ⟨bytesOf k.nkPub⟩
  let nodeDiscoKey   : DiscoKey := ⟨bytesOf k.dsPub⟩
  let nodeMachineKey : MachineKey := ⟨bytesOf k.mpub⟩

  let fd ← tcpConnect host port
  IO.println "node: connected (real TCP)."
  let nodeSess : Control.Channel.Session :=
    { role := .node, spriv := k.mpriv, spub := k.mpub, epriv := k.nEpriv, epub := k.nEpub, peerS := k.sPub }
  let (nodeP1, _o1) := Control.Channel.step nodeSess .fresh .start   -- fresh --start--> awaitResp
  -- 1. send INIT (node ephemeral ‖ node machine static)
  tcpSend fd (k.nEpub ++ k.mpub)
  IO.println "node: sent handshake INIT (ephemeral ‖ machine-static)."
  -- receive RESP (coord ephemeral), drive step to .up
  let some respb ← tcpRecvExact fd 32 recvTimeout | do IO.eprintln "node: no handshake response"; tcpClose fd; return 1
  let (nodeP, _on) := Control.Channel.step nodeSess nodeP1 (.recvResp respb)
  let some nodeTx := (match nodeP with | .up tx => some tx | _ => none)
    | do IO.eprintln "node: handshake did not reach .up"; tcpClose fd; return 1
  IO.println s!"node: handshake UP; send key : {toHex nodeTx.send}"

  -- 2. seal + send RegisterRequest, then MapRequest
  let regReq : RegisterRequest :=
    { version := 1, nodeKey := nodeOverlayKey, oldNodeKey := ⟨[]⟩, machineKey := nodeMachineKey,
      authKey := "tskey-auth-selftest".toUTF8.toList, expiry := 0, ephemeral := false, followup := false }
  let some regFrame := Control.Channel.sealRegReq nodeTx.send nonce0 regReq
    | do IO.eprintln "node: sealRegReq failed"; tcpClose fd; return 1
  sendFrame fd regFrame
  let mapReq : MapRequest :=
    { version := 1, nodeKey := nodeOverlayKey, discoKey := nodeDiscoKey,
      endpoints := [{ addr := [192,168,1,10], port := 41641 }],
      stream := true, omitPeers := false, readOnly := false }
  let some mapFrame := Control.Channel.sealMapReq nodeTx.send nonce0 mapReq
    | do IO.eprintln "node: sealMapReq failed"; tcpClose fd; return 1
  sendFrame fd mapFrame
  IO.println "node: sent sealed RegisterRequest + MapRequest."

  -- 3. recv sealed MapResponse, open, applyDelta, toWgPeers
  let some respFrame ← recvFrame fd | do IO.eprintln "node: no MapResponse"; tcpClose fd; return 1
  let some mresp' := Control.Channel.openMapResp nodeTx.recv nonce0 respFrame
    | do IO.eprintln "node: could not open MapResponse"; tcpClose fd; return 1
  let selfNode : Node :=
    { id := 0, stableID := [], name := "self.example.ts.net".toUTF8.toList, user := 1,
      key := nodeOverlayKey, machine := nodeMachineKey, disco := nodeDiscoKey,
      addresses := [{ addr := [100,64,0,1], bits := 32 }], allowedIPs := [], endpoints := [],
      derp := 1, online := true, keyExpiry := 0, authorized := true }
  let nm0 : NetMap := { self := selfNode, peers := [], dns := DnsConfig.empty, packetFilter := [] }
  let nmApplied := nm0.applyDelta mresp'
  let wgPeers   := nmApplied.toWgPeers
  IO.println s!"node: opened + applied MapResponse ({(baOf respFrame).size}B) -> {nmApplied.peers.length} peer(s), {nmApplied.packetFilter.length} filter rule(s)."
  for p in wgPeers do
    let cidrs := p.allowed.map (fun c => s!"{c.addr}/{c.plen}")
    IO.println s!"node:   WG peer spub={toHex p.spub} allowedIPs={cidrs}"
  tcpClose fd
  if wgPeers.isEmpty then do
    IO.eprintln "node: FAIL — no WG peers programmed"; return 1
  else do
    IO.println "node: DONE — handshake UP, netmap applied, WG peers programmed over real TCP."
    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | ["coord", portS] =>
    match portS.toNat? with
    | some p => coord p.toUInt16
    | none => do IO.eprintln "control-live coord <port>: bad port"; return 1
  | ["node", host, portS] =>
    match portS.toNat? with
    | some p => node host p.toUInt16
    | none => do IO.eprintln "control-live node <host> <port>: bad port"; return 1
  | _ => do
    IO.eprintln "usage: control-live selftest | coord <port> | node <host> <port>"
    return 1

end ControlLive

def main (args : List String) : IO UInt32 := ControlLive.main args
