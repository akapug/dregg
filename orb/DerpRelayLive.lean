/-
# DerpRelayLive — driving the proven DERP relay-forwarding server over real sockets

The `Derp.Relay` model is sans-IO: `RelayState.step` / `RelayState.forward` compute
the routing decision (peer key → connection) and the exact forwarded frame bytes as
pure functions on the proven `Derp` frame codec and the verified `Crypto` crypto_box
login. This executable takes those decisions to real TCP sockets: it runs the relay
server (accept connections, learn each peer's key from its `FrameClientInfo`, and
forward `FrameSendPacket`s peer-to-peer as `FrameRecvPacket`s) and drives two clients
through it.

The forwarding is decided by the PROVEN `Derp.Relay.step`: the relay never chooses a
destination other than the one `RelayState.connOf` returns, and copies the payload
bytes verbatim (`relay_blind`). The relay opens the ClientInfo box only to LEARN the
sender's public key (the registration); it never reads the relayed packet payload.

Modes:
  derp-relay selftest [port]    run relay + two clients in one process; A -> B end to end
  derp-relay serve    [port]    run only the relay (drive it with the `derp-live` clients)

Not part of the trusted core: this is a live cross-check, the relay-server analogue of
`derp-live`. Everything cryptographic/structural/routing is the proven/verified Lean.
-/
import Derp.Relay

open Crypto (x25519Base)

namespace DerpRelayLive

/-! ## The socket seams (untrusted FFI) -/

-- client seam (ffi/derp_net.c)
@[extern "drorb_tcp_connect"]
opaque tcpConnect (host : String) (port : UInt16) : IO UInt32
@[extern "drorb_tcp_send"]
opaque tcpSend (fd : UInt32) (payload : ByteArray) : IO Unit
@[extern "drorb_tcp_recv_exact"]
opaque tcpRecvExact (fd : UInt32) (nbytes : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)
@[extern "drorb_tcp_close"]
opaque tcpClose (fd : UInt32) : IO Unit

-- server seam (ffi/derp_relay_net.c)
@[extern "relay_tcp_listen"]
opaque tcpListen (port : UInt16) : IO UInt32
@[extern "relay_tcp_accept"]
opaque tcpAccept (lfd : UInt32) (timeoutMs : UInt32) : IO (Option UInt32)
@[extern "relay_tcp_send"]
opaque srvSend (fd : UInt32) (payload : ByteArray) : IO Unit
@[extern "relay_tcp_recv_exact"]
opaque srvRecvExact (fd : UInt32) (nbytes : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)
@[extern "relay_tcp_recv_some"]
opaque srvRecvSome (fd : UInt32) (maxBytes : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)
@[extern "relay_poll_readable"]
opaque pollReadable (fdA fdB : UInt32) (timeoutMs : UInt32) : IO UInt32
@[extern "relay_tcp_close"]
opaque srvClose (fd : UInt32) : IO Unit

/-! ## Hex + rendering helpers -/

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

def utf8OrHex (b : ByteArray) : String := (String.fromUTF8? b).getD (toHex b)

def recvTimeout : UInt32 := 5000
def maxLen : Nat := 70000

/-! ## The relay server -/

/-- The relay's fixed server static key (a live-harness constant; a real relay
would persist a generated key). The clients seal their ClientInfo to `serverPub`. -/
def serverSecHex : String :=
  "5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e"

/-- A fixed 24-byte nonce for the relay's ServerInfo box (one box per reply). -/
def serverNonce : ByteArray := ⟨Array.mkArray 24 (0x5b : UInt8)⟩

/-- Read one complete DERP frame off a server-side connection (5-byte header then
the declared payload), reassembled and parsed by the proven `Derp.parseFrame`. -/
def srvReadFrame (fd : UInt32) : IO (Option Derp.Frame) := do
  match ← srvRecvExact fd 5 recvTimeout with
  | none => return none
  | some hb =>
    let len := Derp.be32 (hb.get! 1) (hb.get! 2) (hb.get! 3) (hb.get! 4)
    let payload ← if len == 0 then pure (some ByteArray.empty)
                  else srvRecvExact fd (UInt32.ofNat len) recvTimeout
    match payload with
    | none => return none
    | some pb =>
      match Derp.parseFrame maxLen (hb ++ pb).toList with
      | some (f, _) => return some f
      | none => return none

/-- Does `s` contain a CRLF CRLF (the end of an HTTP header block)? -/
def hasCrlfCrlf (s : List UInt8) : Bool :=
  (s.zip (s.drop 1) |>.zip ((s.drop 2).zip (s.drop 3))).any
    (fun ((a, b), (c, d)) => a == 13 ∧ b == 10 ∧ c == 13 ∧ d == 10)

/-- Drain the client's HTTP Upgrade preamble (`GET /derp … \r\n\r\n`) so the next
bytes on the wire are frames. Reads chunks until the blank-line terminator. -/
partial def drainUpgrade (fd : UInt32) (acc : ByteArray) (fuel : Nat) : IO Bool := do
  if fuel == 0 then return false
  match ← srvRecvSome fd 2048 recvTimeout with
  | none => return false
  | some chunk =>
    let acc := acc ++ chunk
    if hasCrlfCrlf acc.toList then return true
    else drainUpgrade fd acc (fuel - 1)

/-- Run the relay's side of the login handshake on a freshly accepted connection,
returning the peer's public key (learned by opening its ClientInfo). This is the
registration input: the key the relay will route to `fd`. -/
def relayHandshake (serverSec serverPub : ByteArray) (fd : UInt32) :
    IO (Option Derp.Bytes) := do
  if !(← drainUpgrade fd ByteArray.empty 8) then IO.eprintln "[relay] no HTTP upgrade"; return none
  -- 1. send FrameServerKey greeting (magic ‖ serverPub)
  let skFrame : Derp.Frame :=
    { ftype := .serverKey, payload := Derp.serverKeyPayload (Derp.bytesOf serverPub) }
  srvSend fd (Derp.baOf (Derp.serializeFrame skFrame))
  -- 2. read FrameClientInfo, open it to LEARN the peer key (registration)
  match ← srvReadFrame fd with
  | none => IO.eprintln "[relay] no FrameClientInfo"; return none
  | some cif =>
    if cif.ftype != Derp.FrameType.clientInfo then
      IO.eprintln s!"[relay] expected clientInfo, got {repr cif.ftype}"; return none
    match Derp.openClientInfo serverSec cif.payload with
    | none => IO.eprintln "[relay] openClientInfo REJECTED"; return none
    | some (clientPubL, infoL) =>
      -- 3. reply FrameServerInfo, sealed back to the client (proven Derp.buildServerInfo)
      match Derp.buildServerInfo (Derp.baOf clientPubL) serverSec serverNonce (Derp.baOf infoL) with
      | none => IO.eprintln "[relay] buildServerInfo failed"; return none
      | some sif =>
        srvSend fd (Derp.baOf (Derp.serializeFrame sif))
        IO.println s!"[relay] registered peer {toHex (Derp.baOf clientPubL)}"
        return some clientPubL

/-- Deliver every `Delivery` the proven relay emits to its destination connection.
`fds` maps a `ConnId` to its socket. The frame bytes come straight from the proven
`Derp.serializeFrame`; the routing choice from the proven `Derp.Relay.step`. -/
def emitDeliveries (fds : Array UInt32) (ds : List Derp.Relay.Delivery) : IO Unit := do
  for d in ds do
    match fds[d.dst]? with
    | some dfd =>
      srvSend dfd (Derp.baOf (Derp.serializeFrame d.frame))
      IO.println s!"[relay] forwarded {repr d.frame.ftype} to conn {d.dst} ({d.frame.payload.length}B)"
    | none => IO.eprintln s!"[relay] delivery to unknown conn {d.dst}"

/-- The forward loop: whichever conn speaks, run the proven `Derp.Relay.step` and
emit its deliveries. Returns `true` once a frame is forwarded. -/
partial def forwardLoop (fd0 fd1 : UInt32) (fds : Array UInt32)
    (st : Derp.Relay.RelayState) (fuel : Nat) : IO Bool := do
  if fuel == 0 then return false
  let which ← pollReadable fd0 fd1 8000
  if which == 0xFFFFFFFF then IO.eprintln "[relay] poll timeout"; return false
  let (srcConn, srcFd) := if which == 0 then ((0 : Nat), fd0) else ((1 : Nat), fd1)
  match ← srvReadFrame srcFd with
  | none => IO.eprintln "[relay] read frame failed"; return false
  | some f =>
    if f.ftype == Derp.FrameType.sendPacket then
      match Derp.splitKeyed f.payload with
      | none => IO.eprintln "[relay] short SendPacket"; forwardLoop fd0 fd1 fds st (fuel - 1)
      | some (dstKey, pkt) =>
        -- THE PROVEN ROUTING DECISION: Derp.Relay.step
        let (st', ds) := Derp.Relay.step st (.sendPacket srcConn dstKey pkt)
        emitDeliveries fds ds
        if ds.isEmpty then forwardLoop fd0 fd1 fds st' (fuel - 1) else return true
    else forwardLoop fd0 fd1 fds st (fuel - 1)

/-- The relay: accept two clients, register each (by opening its ClientInfo), then
forward one `SendPacket` through the proven `Derp.Relay.step`. Runs until a frame is
forwarded or the poll times out. Returns `true` on a successful forward. -/
def runRelay (port : UInt16) : IO Bool := do
  let serverSec := ofHex serverSecHex
  let some serverPub := (← pure (x25519Base serverSec)) | do
    IO.eprintln "[relay] x25519Base(serverSec) failed"; return false
  let lfd ← tcpListen port
  IO.println s!"[relay] listening on 127.0.0.1:{port}  pub {toHex serverPub}"
  -- accept + register conn 0
  let some fd0 := (← tcpAccept lfd 8000) | do IO.eprintln "[relay] accept 0 timeout"; return false
  let some key0 := (← relayHandshake serverSec serverPub fd0) | return false
  -- accept + register conn 1
  let some fd1 := (← tcpAccept lfd 8000) | do IO.eprintln "[relay] accept 1 timeout"; return false
  let some key1 := (← relayHandshake serverSec serverPub fd1) | return false
  let fds := #[fd0, fd1]
  -- build the proven routing table: conn 0 -> key0, conn 1 -> key1
  let s0 := (Derp.Relay.step Derp.Relay.RelayState.empty (.clientInfo 0 key0)).1
  let s1 := (Derp.Relay.step s0 (.clientInfo 1 key1)).1
  IO.println "[relay] both peers registered; entering forward loop"
  let ok ← forwardLoop fd0 fd1 fds s1 16
  srvClose fd0; srvClose fd1; srvClose lfd
  return ok

/-! ## The client side (drives the relay, for the self-contained check) -/

def clientNonce : ByteArray := ⟨Array.mkArray 24 (0x2a : UInt8)⟩

def upgradeRequest : ByteArray :=
  "GET /derp HTTP/1.1\r\nHost: 127.0.0.1\r\nUpgrade: DERP\r\nConnection: Upgrade\r\nDerp-Fast-Start: 1\r\n\r\n".toUTF8

def cliReadFrame (fd : UInt32) : IO (Option Derp.Frame) := do
  match ← tcpRecvExact fd 5 recvTimeout with
  | none => return none
  | some hb =>
    let len := Derp.be32 (hb.get! 1) (hb.get! 2) (hb.get! 3) (hb.get! 4)
    let payload ← if len == 0 then pure (some ByteArray.empty)
                  else tcpRecvExact fd (UInt32.ofNat len) recvTimeout
    match payload with
    | none => return none
    | some pb =>
      match Derp.parseFrame maxLen (hb ++ pb).toList with
      | some (f, _) => return some f
      | none => return none

/-- One client's full login handshake against the relay; returns its fd. -/
def clientLogin (label : String) (port : UInt16) (priv pub : ByteArray) :
    IO (Option UInt32) := do
  let fd ← tcpConnect "127.0.0.1" port
  tcpSend fd upgradeRequest
  match ← cliReadFrame fd with
  | none => IO.eprintln s!"[{label}] no FrameServerKey"; return none
  | some skf =>
    match Derp.parseServerKey skf.payload with
    | none => IO.eprintln s!"[{label}] bad ServerKey magic"; return none
    | some serverPubL =>
      let serverPub := Derp.baOf serverPubL
      let info := "{\"version\":2}".toUTF8
      match Derp.buildClientInfo pub serverPub priv clientNonce info with
      | none => IO.eprintln s!"[{label}] buildClientInfo failed"; return none
      | some cif =>
        tcpSend fd (Derp.baOf (Derp.serializeFrame cif))
        match ← cliReadFrame fd with
        | none => IO.eprintln s!"[{label}] no FrameServerInfo"; return none
        | some sif =>
          match Derp.openServerInfo serverPub priv sif.payload with
          | none => IO.eprintln s!"[{label}] openServerInfo REJECTED"; return none
          | some _ =>
            IO.println s!"[{label}] login complete (pub {toHex pub})"
            return some fd

/-- The self-contained end-to-end check: run the relay in a background task, log in
two clients B then A, have A send a packet addressed to B's key, and confirm B reads
it back as a RecvPacket carrying A's key and the verbatim packet. -/
def selftest (port : UInt16) : IO UInt32 := do
  let privA := ofHex "a01111111111111111111111111111111111111111111111111111111111111a"
  let privB := ofHex "b02222222222222222222222222222222222222222222222222222222222222b"
  let some pubA := (← pure (x25519Base privA)) | do IO.eprintln "x25519Base(A) failed"; return 1
  let some pubB := (← pure (x25519Base privB)) | do IO.eprintln "x25519Base(B) failed"; return 1
  IO.println s!"client A pub {toHex pubA}"
  IO.println s!"client B pub {toHex pubB}\n"
  -- start the relay in the background
  let relayTask ← IO.asTask (runRelay port)
  -- give the listener a moment to bind
  IO.sleep 300
  IO.println "=== client B login ==="
  let some fdB := (← clientLogin "B" port privB pubB) | do IO.eprintln "B login failed"; return 1
  IO.println "\n=== client A login ==="
  let some fdA := (← clientLogin "A" port privA pubA) | do tcpClose fdB; IO.eprintln "A login failed"; return 1
  IO.println "\n=== relay a real frame: A -> (relay) -> B ==="
  let packet := "hello-through-my-own-DERP-relay".toUTF8
  let sendFrame : Derp.Frame :=
    { ftype := .sendPacket, payload := Derp.bytesOf pubB ++ Derp.bytesOf packet }
  tcpSend fdA (Derp.baOf (Derp.serializeFrame sendFrame))
  IO.println s!"[A] -> FrameSendPacket to B ({(Derp.serializeFrame sendFrame).length}B)"
  -- B reads its RecvPacket
  let mut result : UInt32 := 1
  match ← cliReadFrame fdB with
  | none => IO.eprintln "[B] no frame arrived"
  | some rf =>
    if rf.ftype != Derp.FrameType.recvPacket then
      IO.eprintln s!"[B] expected recvPacket, got {repr rf.ftype}"
    else
      match Derp.splitKeyed rf.payload with
      | none => IO.eprintln "[B] short RecvPacket"
      | some (srcPub, relayed) =>
        IO.println s!"[B] <- FrameRecvPacket  src {toHex (Derp.baOf srcPub)}"
        IO.println s!"[B]    relayed packet   : {utf8OrHex (Derp.baOf relayed)}"
        let okSrc := srcPub == Derp.bytesOf pubA
        let okPkt := relayed == Derp.bytesOf packet
        IO.println s!"\n    src == A pubkey : {okSrc}"
        IO.println s!"    packet verbatim : {okPkt}"
        if okSrc ∧ okPkt then
          IO.println "\nRELAY COMPLETE — a real frame traversed MY OWN DERP relay, A -> B."
          result := 0
        else IO.eprintln "\nrelayed frame did not match"
  tcpClose fdA; tcpClose fdB
  let relayOk ← IO.wait relayTask
  match relayOk with
  | .ok true => pure ()
  | _ => IO.eprintln "[relay] did not report a successful forward"
  return result

def main (args : List String) : IO UInt32 := do
  match args with
  | "serve" :: rest =>
    let port := (rest.getD 0 "3340").toNat?.getD 3340 |>.toUInt16
    let ok ← runRelay port
    return (if ok then 0 else 1)
  | "selftest" :: rest =>
    let port := (rest.getD 0 "3399").toNat?.getD 3399 |>.toUInt16
    selftest port
  | _ =>
    -- default: self-contained end-to-end check
    selftest 3399

end DerpRelayLive

def main (args : List String) : IO UInt32 := DerpRelayLive.main args
