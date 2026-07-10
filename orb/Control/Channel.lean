import Control
import Wireguard
import Crypto
/-!
# Control.Channel — the ts2021 Noise-IK control channel

The `Control` foundation models the coordination server as an in-memory
transition system: a node registers, is authorized, and polls for its netmap.
But those `RegisterRequest` / `MapRequest` / `MapResponse` messages have to
*travel* between the node and the coordination server over a secure transport.
This module is that transport — the **ts2021** control protocol.

ts2021 is the public Tailscale control-plane protocol (`control/controlbase` and
`control/controlhttp` in github.com/tailscale/tailscale, BSD-3; the community
coordination server github.com/juanfont/headscale, BSD-3, speaks the responder
side). It is a **Noise IK** handshake — `Noise_IK_25519_ChaChaPoly_BLAKE2s` —
run over HTTP, after which the coordination messages ride as AEAD-sealed control
frames. Everything here is derived from that public specification and source; it
is an independent clean-room model.

## The two ends

  * The **node** (client) is the Noise **initiator**. Its static key is its
    **machine key** (`Control.MachineKey`) — the durable device identity. It
    learns the coordination server's static public key out of band (from the
    login server), so it can address the responder.
  * The **coordination server** is the Noise **responder**. Its static key is
    the fixed server key every node trusts.

The IK pattern is exactly right for this: the initiator already knows the
responder's static key (`I`nitiator-`K`nown), and the initiator transmits its own
static (machine) key *encrypted* inside the first message, so the machine
identity is never exposed on the wire and is authenticated to the server.

## What is reused, not re-derived (`Wireguard.Noise`)

drorb already has a verified Noise IK handshake — WireGuard's `Noise_IKpsk2`
variant in `Wireguard.Noise`, over the same primitives ts2021 uses (X25519 +
ChaCha20-Poly1305 + BLAKE2s). We **reuse** that machinery rather than re-derive
crypto:

  * `Wireguard.Noise.initiatorChainingKey` / `responderChainingKey` — the DH
    ratchet computed from opposite ends.
  * `Wireguard.Noise.transportKeys` — the 64-byte `KDF2` transport material.
  * `Wireguard.Noise.wg_transport_keys_agree` — **both peers derive identical
    transport keys** (the X25519 agreement, discharged by `Crypto`).
  * `Wireguard.Noise.sealStatic` / `wg_static_key_authenticated` /
    `wg_static_key_unforgeable` — the AEAD-sealed static (machine) key and its
    forgery-resistance.

ts2021 is Noise **IK** (no preshared key), where WireGuard is IK**psk2**. We
reuse the IKpsk2 ratchet with its `psk` slot instantiated at a fixed *public*
constant (`tsPsk`). A public post-mix of the chaining key does not weaken key
agreement — both peers apply the identical public step — so the reused
`wg_transport_keys_agree` transfers verbatim, and the security still rests
entirely on the DH chain of the static + ephemeral keys (one static being the
machine key). The byte-exact ts2021 chaining-key constant (dropping the psk mix,
plus the precise transcript-hash binding) is the residual to pin for wire-level
interop; the key-agreement / authenticity SECURITY properties hold as proven.

## Trust surface

No new crypto axioms. The channel's guarantees compose the `Crypto` assumptions
(`x25519_dh_agree`, `chacha_open_seal_roundtrip`, `chacha_open_authentic`)
already discharged by HACL*/EverCrypt upstream, exactly as `Wireguard` and
`Disco` do. This module touches no serve / dataplane file; it composes with the
`Control` foundation types.
-/

namespace Control.Channel

open Wireguard

/-! ## §0  Byte-view helpers and protocol constants

The AEAD primitives operate on `ByteArray`; the codec algebra (`Control.Bytes =
List UInt8`) operates on lists. These two adapters convert, with the same
round-trip laws `Disco` uses. -/

/-- `List UInt8` view of a `ByteArray` (its backing array as a list). -/
def bytesOf (b : ByteArray) : Control.Bytes := b.data.toList

/-- Repack a byte list into a `ByteArray`. -/
def baOf (l : Control.Bytes) : ByteArray := ⟨l.toArray⟩

@[simp] theorem baOf_bytesOf (b : ByteArray) : baOf (bytesOf b) = b := by
  show (ByteArray.mk b.data.toList.toArray) = b
  simp

@[simp] theorem bytesOf_baOf (l : Control.Bytes) : bytesOf (baOf l) = l := by
  show (ByteArray.mk l.toArray).data.toList = l
  simp

/-- The ts2021 control-protocol version (`controlbase` protocol version). -/
def protocolVersion : Nat := 1

/-- The Noise handshake name for ts2021 — Noise IK, X25519, ChaCha20-Poly1305,
BLAKE2s (`control/controlbase`). -/
def protocolName : ByteArray := "Noise_IK_25519_ChaChaPoly_BLAKE2s".toUTF8

/-- The fixed public constant instantiating the reused IKpsk2 ratchet's `psk`
slot (ts2021 is psk-free — see the module header). 32 zero bytes: a public value
both peers mix identically, so it is inert to key agreement. -/
def tsPsk : ByteArray := ⟨Array.mkArray 32 (0 : UInt8)⟩

/-! ## §1  The Noise-IK transport-key derivation (reused machinery)

Both ends run the reused `Wireguard.Noise` ratchet, differing only in which end
computes the four DH secrets. The 64-byte output splits into the two directional
transport keys. -/

/-- One direction's transport keys: this peer's send key and receive key. -/
structure TxKeys where
  send : ByteArray
  recv : ByteArray

/-- First 32 bytes of the 64-byte transport material (`T_send_i`). -/
def firstHalf (m : ByteArray) : ByteArray := m.extract 0 32
/-- Second 32 bytes of the 64-byte transport material (`T_recv_i`). -/
def secondHalf (m : ByteArray) : ByteArray := m.extract 32 64

/-- The **initiator** (node) uses the first half to send, the second to receive
(`controlbase` orientation). -/
def initiatorTx (m : ByteArray) : TxKeys := { send := firstHalf m, recv := secondHalf m }
/-- The **responder** (coordination server) uses the halves swapped, so its send
key is the initiator's receive key and vice versa. -/
def responderTx (m : ByteArray) : TxKeys := { send := secondHalf m, recv := firstHalf m }

/-- The node's (initiator's) 64-byte transport material: it holds its machine
static `mpriv` and ephemeral `epriv`, was told the server static `spubS`, and
learns the server ephemeral `epubS` from the response. -/
def nodeMaterial (mpriv epriv epub spubS epubS : ByteArray) : Option ByteArray :=
  Noise.transportKeys (Noise.initiatorChainingKey mpriv epriv epub spubS epubS tsPsk)

/-- The coordination server's (responder's) 64-byte transport material: it holds
its static `spriv` and ephemeral `epriv`, and learns the node's machine static
`mpub` (by decrypting the initiation) and ephemeral `epubN` (in the clear). -/
def serverMaterial (spriv epriv mpub epubN epubS : ByteArray) : Option ByteArray :=
  Noise.transportKeys (Noise.responderChainingKey spriv epriv mpub epubN epubS tsPsk)

/-- **The handshake key agreement.** Given well-formed keypairs (each public
point is its scalar's X25519 base multiple), the node and the coordination
server — computing their DH secrets from opposite ends — derive the *same*
64-byte transport material. Reuses `Wireguard.Noise.wg_transport_keys_agree`
(the X25519 agreement, discharged by `Crypto`); the ts2021 channel inherits the
verified WireGuard Noise guarantee directly. -/
theorem handshake_keys_agree
    (mpriv epriv spriv esPriv mpub epub spubS epubS : ByteArray)
    (hM : Crypto.x25519Base mpriv = some mpub)
    (hE : Crypto.x25519Base epriv = some epub)
    (hS : Crypto.x25519Base spriv = some spubS)
    (hES : Crypto.x25519Base esPriv = some epubS) :
    nodeMaterial mpriv epriv epub spubS epubS
      = serverMaterial spriv esPriv mpub epub epubS := by
  unfold nodeMaterial serverMaterial
  exact Noise.wg_transport_keys_agree mpriv epriv spriv esPriv mpub epub spubS epubS tsPsk
    hM hE hS hES

/-- **The directional keys agree.** From one shared 64-byte material, the node's
send key is the server's receive key and the node's receive key is the server's
send key — so each side can open what the other sealed. -/
theorem tx_directions_agree (m : ByteArray) :
    (initiatorTx m).send = (responderTx m).recv ∧
    (initiatorTx m).recv = (responderTx m).send :=
  ⟨rfl, rfl⟩

/-! ## §2  The handshake as a transition system

A compact transition system in the shape of `TlsHandshake.serverStep` and the
WireGuard handshake FSM: a `Phase`, a role-tagged `Session`, and a total `step`
that consumes handshake events and reaches `established` (`.up`) carrying the
derived transport keys. The safety facts mirror the WireGuard handshake's
`wg_no_transport_before_handshake` / `wg_established_needs_handshake`. -/

/-- Which end of the handshake this peer plays. -/
inductive Role where
  | node   -- the initiator (client), machine-key static identity
  | coord  -- the responder (coordination server)
deriving DecidableEq, Repr

/-- A peer's handshake session material. -/
structure Session where
  role  : Role
  /-- Own static private scalar (node: machine key; coord: server key). -/
  spriv : ByteArray
  /-- Own static public point. -/
  spub  : ByteArray
  /-- Own ephemeral private scalar. -/
  epriv : ByteArray
  /-- Own ephemeral public point. -/
  epub  : ByteArray
  /-- Known peer static public (node: the server key; unused by coord). -/
  peerS : ByteArray

/-- Handshake phase. `up` carries the derived directional transport keys. -/
inductive Phase where
  /-- No handshake in progress. -/
  | fresh
  /-- Node emitted the initiation, awaiting the server response. -/
  | awaitResp
  /-- Handshake complete; the channel is up with these transport keys. -/
  | up (tx : TxKeys)

/-- Events the environment can deliver to the handshake. -/
inductive Ev where
  /-- Begin (node only): emit the initiation. -/
  | start
  /-- The coordination server receives an initiation carrying the node's
  ephemeral public and its (decrypted) machine static public. -/
  | recvInit (epubN mpub : ByteArray)
  /-- The node receives the server's response carrying the server ephemeral. -/
  | recvResp (epubS : ByteArray)

/-- Handshake outputs (the wire sends). -/
inductive Out where
  /-- Node → server: the initiation carrying the node ephemeral public. -/
  | sendInit (epub : ByteArray)
  /-- Server → node: the response carrying the server ephemeral public. -/
  | sendResp (epub : ByteArray)
  /-- Nothing to emit. -/
  | idle

/-- **The handshake transition.** Total on phase × event. The node begins from
`.fresh` on `.start`; the coordination server completes from `.fresh` on
`.recvInit` (deriving responder transport keys and learning the machine key);
the node completes from `.awaitResp` on `.recvResp` (deriving initiator
transport keys). Any other pairing is inert. -/
def step (ss : Session) : Phase → Ev → Phase × Out
  | .fresh, .start =>
    match ss.role with
    | .node  => (.awaitResp, .sendInit ss.epub)
    | .coord => (.fresh, .idle)
  | .fresh, .recvInit epubN mpub =>
    match serverMaterial ss.spriv ss.epriv mpub epubN ss.epub with
    | some m => (.up (responderTx m), .sendResp ss.epub)
    | none   => (.fresh, .idle)
  | .awaitResp, .recvResp epubS =>
    match nodeMaterial ss.spriv ss.epriv ss.epub ss.peerS epubS with
    | some m => (.up (initiatorTx m), .idle)
    | none   => (.awaitResp, .idle)
  | p, _ => (p, .idle)

/-- States reachable under some event trace from `.fresh`. -/
inductive Reachable (ss : Session) : Phase → Prop where
  | fresh : Reachable ss .fresh
  | step {p : Phase} (h : Reachable ss p) (e : Ev) : Reachable ss (step ss p e).1

/-- **No channel before the handshake completes.** Starting the handshake from
`.fresh` never yields an established (`.up`) channel — `.start` only *emits* the
initiation; it derives no transport keys. (The WireGuard-handshake analog of
`wg_no_transport_before_handshake`.) -/
theorem channel_no_up_from_start (ss : Session) (tx : TxKeys) :
    (step ss .fresh .start).1 ≠ .up tx := by
  simp only [step]
  cases ss.role <;> simp

/-- **Entering the channel is a handshake completion.** If a step takes a
not-yet-established phase to `.up`, the event was a handshake message —
`recvInit` (server side) or `recvResp` (node side) — never `.start`. The
transport keys appear only on completing the Noise exchange. (The analog of
`wg_established_needs_handshake`.) -/
theorem channel_up_needs_handshake (ss : Session) (p : Phase) (e : Ev) (tx : TxKeys)
    (hp : ∀ tx0, p ≠ .up tx0)
    (h : (step ss p e).1 = .up tx) :
    (∃ epubN mpub, e = .recvInit epubN mpub) ∨ (∃ epubS, e = .recvResp epubS) := by
  cases p with
  | up tx0 => exact absurd rfl (hp tx0)
  | fresh =>
    cases e with
    | start =>
      exfalso; exact channel_no_up_from_start ss tx h
    | recvInit epubN mpub => exact Or.inl ⟨epubN, mpub, rfl⟩
    | recvResp epubS =>
      -- fresh + recvResp is inert (catch-all), stays fresh
      simp only [step] at h; exact Phase.noConfusion h
  | awaitResp =>
    cases e with
    | start => simp only [step] at h; exact Phase.noConfusion h
    | recvInit epubN mpub => simp only [step] at h; exact Phase.noConfusion h
    | recvResp epubS => exact Or.inr ⟨epubS, rfl⟩

/-- **The established transport keys agree across the two ends.** If the node
completes with the initiator keys derived from material `m`, and the server
completes with the responder keys derived from the *same* material (guaranteed by
`handshake_keys_agree` under well-formed keypairs), then the node's send key is
the server's receive key and vice versa — the channel is bidirectionally
keyed. -/
theorem channel_established_keys_agree
    (mpriv epriv spriv esPriv mpub epub spubS epubS m : ByteArray)
    (hM : Crypto.x25519Base mpriv = some mpub)
    (hE : Crypto.x25519Base epriv = some epub)
    (hS : Crypto.x25519Base spriv = some spubS)
    (hES : Crypto.x25519Base esPriv = some epubS)
    (hNode : nodeMaterial mpriv epriv epub spubS epubS = some m) :
    serverMaterial spriv esPriv mpub epub epubS = some m ∧
    (initiatorTx m).send = (responderTx m).recv ∧
    (initiatorTx m).recv = (responderTx m).send := by
  refine ⟨?_, tx_directions_agree m⟩
  rw [← handshake_keys_agree mpriv epriv spriv esPriv mpub epub spubS epubS hM hE hS hES]
  exact hNode

/-! ## §3  The sealed control channel — frame codec + AEAD

Post-handshake, a control message is AEAD-sealed under a directional transport
key and framed as a ts2021 control **record**: a 1-byte record tag then the
length-prefixed ciphertext (`controlbase` frames each post-handshake message with
a type byte and a length). The frame codec reuses `Control`'s length-prefixed
byte-string codec (`putBytes` / `getBytes`), so its round-trip chains from the
already-proven `getBytes_putBytes`. -/

/-- The record message type in the ts2021 framing (`controlbase` `msgTypeRecord`). -/
def recordTag : UInt8 := 3

/-- Frame a ciphertext: record tag, then the length-prefixed ciphertext bytes. -/
def encodeFrame (ct : Control.Bytes) : Control.Bytes := recordTag :: Control.putBytes ct

/-- Parse a control frame: require the record tag, then read the length-prefixed
ciphertext. -/
def parseFrame (bs : Control.Bytes) : Option Control.Bytes :=
  match bs with
  | [] => none
  | t :: rest => if t == recordTag then (Control.getBytes rest).map (·.1) else none

/-- **Frame round-trip.** Parsing an encoded frame recovers the ciphertext
exactly. -/
theorem frame_roundtrip (ct : Control.Bytes) : parseFrame (encodeFrame ct) = some ct := by
  unfold parseFrame encodeFrame
  simp only [beq_self_eq_true, if_true]
  rw [show Control.putBytes ct = Control.putBytes ct ++ [] from (List.append_nil _).symm,
      Control.getBytes_putBytes]
  simp

/-- The all-zero 12-byte AEAD nonce (the record counter starts at 0 under each
transport key; the counter is carried in the first bytes on the real wire). -/
def nonce0 : ByteArray := ⟨Array.mkArray 12 (0 : UInt8)⟩

/-- **Seal** a control payload under a directional transport key and nonce, and
frame it. `none` only on a bad key/nonce size (the AEAD's contract). -/
def sealFrame (key nonce : ByteArray) (payload : Control.Bytes) : Option Control.Bytes :=
  match Crypto.chachaSeal key nonce ByteArray.empty (baOf payload) with
  | some ct => some (encodeFrame (bytesOf ct))
  | none    => none

/-- **Open** a control frame under a directional transport key and nonce.
`none` on a malformed frame OR an authentication failure (indistinguishable, as
the AEAD requires). -/
def openFrame (key nonce : ByteArray) (frame : Control.Bytes) : Option Control.Bytes :=
  match parseFrame frame with
  | some ct =>
    match Crypto.chachaOpen key nonce ByteArray.empty (baOf ct) with
    | some pt => some (bytesOf pt)
    | none    => none
  | none => none

/-- **The channel round-trip.** A payload sealed by one side under its send key
opens, on the other side under the matching receive key (equal by
`channel_established_keys_agree`), to *exactly* the same payload. This is the
control-plane analog of `Disco.disco_seal_open`: the bytes one end puts on the
wire are precisely what the other decodes. -/
theorem seal_open (sk rk nonce : ByteArray) (payload : Control.Bytes)
    (hk : sk = rk) {frame : Control.Bytes}
    (hs : sealFrame sk nonce payload = some frame) :
    openFrame rk nonce frame = some payload := by
  subst hk
  unfold sealFrame at hs
  cases hseal : Crypto.chachaSeal sk nonce ByteArray.empty (baOf payload) with
  | none => rw [hseal] at hs; simp at hs
  | some ct =>
    rw [hseal] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    have hopen : Crypto.chachaOpen sk nonce ByteArray.empty ct = some (baOf payload) :=
      Crypto.Assumptions.chacha_open_seal_roundtrip sk nonce ByteArray.empty
        (baOf payload) ct hseal
    simp only [openFrame, frame_roundtrip, baOf_bytesOf, hopen, bytesOf_baOf]

/-! ## §4  Carrying the `Control` messages

The channel carries the coordination messages: `RegisterRequest` and
`MapRequest` node→server, `RegisterResponse` and `MapResponse` server→node.
Each has a byte-level codec (`Control`'s for the requests/response; a codec built
here for `MapResponse`), so a message sealed on one end decodes on the other. -/

/-! ### A `MapResponse` codec

`Control` fixes `MapResponse` but not its codec (its `full` case carries a whole
`NetMap`, which does have a codec). We add the missing codec: a tag byte then the
constructor payload, with an `Option` field codec for `PeerChange`. -/

/-- Optional-field codec: a presence byte then the value's encoding. -/
def putOpt {α} (e : α → Control.Bytes) : Option α → Control.Bytes
  | none   => [0]
  | some a => 1 :: e a

def getOpt {α} (d : Control.Bytes → Option (α × Control.Bytes)) :
    Control.Bytes → Option (Option α × Control.Bytes)
  | []        => none
  | b :: rest => if b == 0 then some (none, rest) else (d rest).map (fun p => (some p.1, p.2))

theorem getOpt_put {α} (e : α → Control.Bytes) (d : Control.Bytes → Option (α × Control.Bytes))
    (hrt : ∀ a t, d (e a ++ t) = some (a, t)) (o : Option α) (tail : Control.Bytes) :
    getOpt d (putOpt e o ++ tail) = some (o, tail) := by
  cases o with
  | none => simp [putOpt, getOpt]
  | some a => simp only [putOpt, getOpt, List.cons_append]; rw [if_neg (by decide), hrt]; rfl

/-- A `PeerChange` codec (the field-level peer delta). -/
def putPeerChange (c : Control.PeerChange) : Control.Bytes :=
  Control.putNat c.nodeID ++ putOpt Control.putBool c.online ++
  putOpt (Control.putSeq Control.putEndpoint) c.endpoints ++
  putOpt Control.putNodeKey c.key

def getPeerChange (bs : Control.Bytes) : Option (Control.PeerChange × Control.Bytes) := do
  let (nodeID, r) ← Control.getNat bs
  let (online, r) ← getOpt Control.getBool r
  let (endpoints, r) ← getOpt (Control.getSeq Control.getEndpoint) r
  let (key, r) ← getOpt Control.getNodeKey r
  some (⟨nodeID, online, endpoints, key⟩, r)

theorem getPeerChange_put (c : Control.PeerChange) (t : Control.Bytes) :
    getPeerChange (putPeerChange c ++ t) = some (c, t) := by
  obtain ⟨nodeID, online, endpoints, key⟩ := c
  simp [putPeerChange, getPeerChange, List.append_assoc, Control.getNat_putNat,
    getOpt_put Control.putBool Control.getBool Control.getBool_putBool,
    getOpt_put (Control.putSeq Control.putEndpoint) (Control.getSeq Control.getEndpoint)
      (Control.getSeq_putSeq Control.putEndpoint Control.getEndpoint Control.getEndpoint_put),
    getOpt_put Control.putNodeKey Control.getNodeKey Control.getNodeKey_put]

/-- The `MapResponse` codec: `full` (tag 0) carries a `NetMap`; `delta` (tag 1)
carries changed nodes, removed ids, and peer patches; `keepAlive` (tag 2) is bare. -/
def putMapResp : Control.MapResponse → Control.Bytes
  | .full nm => 0 :: Control.putNetMap nm
  | .delta changed removed patch =>
      1 :: (Control.putSeq Control.putNode changed ++ Control.putSeq Control.putNat removed ++
            Control.putSeq putPeerChange patch)
  | .keepAlive => [2]

def getMapResp (bs : Control.Bytes) : Option (Control.MapResponse × Control.Bytes) :=
  match bs with
  | [] => none
  | t :: rest =>
    if t == 0 then
      (Control.getNetMap rest).map (fun p => (.full p.1, p.2))
    else if t == 1 then do
      let (changed, r) ← Control.getSeq Control.getNode rest
      let (removed, r) ← Control.getSeq Control.getNat r
      let (patch, r) ← Control.getSeq getPeerChange r
      some (.delta changed removed patch, r)
    else if t == 2 then some (.keepAlive, rest)
    else none

theorem getMapResp_put (m : Control.MapResponse) (t : Control.Bytes) :
    getMapResp (putMapResp m ++ t) = some (m, t) := by
  cases m with
  | full nm =>
    simp only [putMapResp, getMapResp, List.cons_append]
    rw [if_pos (by decide)]
    rw [Control.getNetMap_put]; rfl
  | delta changed removed patch =>
    simp only [putMapResp, getMapResp, List.cons_append, List.append_assoc]
    rw [if_neg (by decide), if_pos (by decide)]
    simp [Control.getSeq_putSeq Control.putNode Control.getNode Control.getNode_put,
      Control.getSeq_putSeq Control.putNat Control.getNat Control.getNat_putNat,
      Control.getSeq_putSeq putPeerChange getPeerChange getPeerChange_put]
  | keepAlive =>
    simp only [putMapResp, getMapResp, List.cons_append, List.nil_append]
    rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]

/-! ### Typed message channel round-trips

Each seals a `Control` message through the channel and recovers it on the peer,
composing `seal_open` with the message codec's round-trip. The `hk : sk = rk`
hypothesis is the directional key agreement discharged by
`channel_established_keys_agree`. -/

/-- Seal a `RegisterRequest` (node→server). -/
def sealRegReq (key nonce : ByteArray) (q : Control.RegisterRequest) : Option Control.Bytes :=
  sealFrame key nonce (Control.putRegReq q)
/-- Open a control frame as a `RegisterRequest`. -/
def openRegReq (key nonce : ByteArray) (frame : Control.Bytes) : Option Control.RegisterRequest :=
  (openFrame key nonce frame).bind (fun bs => (Control.getRegReq bs).map (·.1))

/-- **`RegisterRequest` round-trips through the channel.** -/
theorem regReq_channel_roundtrip (sk rk nonce : ByteArray) (q : Control.RegisterRequest)
    (hk : sk = rk) {frame : Control.Bytes} (hs : sealRegReq sk nonce q = some frame) :
    openRegReq rk nonce frame = some q := by
  unfold sealRegReq at hs
  have hof := seal_open sk rk nonce (Control.putRegReq q) hk hs
  have hg : Control.getRegReq (Control.putRegReq q) = some (q, []) := by
    have := Control.getRegReq_put q []; rwa [List.append_nil] at this
  simp [openRegReq, hof, hg]

/-- Seal a `MapRequest` (node→server). -/
def sealMapReq (key nonce : ByteArray) (q : Control.MapRequest) : Option Control.Bytes :=
  sealFrame key nonce (Control.putMapReq q)
/-- Open a control frame as a `MapRequest`. -/
def openMapReq (key nonce : ByteArray) (frame : Control.Bytes) : Option Control.MapRequest :=
  (openFrame key nonce frame).bind (fun bs => (Control.getMapReq bs).map (·.1))

/-- **`MapRequest` round-trips through the channel.** -/
theorem mapReq_channel_roundtrip (sk rk nonce : ByteArray) (q : Control.MapRequest)
    (hk : sk = rk) {frame : Control.Bytes} (hs : sealMapReq sk nonce q = some frame) :
    openMapReq rk nonce frame = some q := by
  unfold sealMapReq at hs
  have hof := seal_open sk rk nonce (Control.putMapReq q) hk hs
  have hg : Control.getMapReq (Control.putMapReq q) = some (q, []) := by
    have := Control.getMapReq_put q []; rwa [List.append_nil] at this
  simp [openMapReq, hof, hg]

/-- Seal a `RegisterResponse` (server→node). -/
def sealRegResp (key nonce : ByteArray) (r : Control.RegisterResponse) : Option Control.Bytes :=
  sealFrame key nonce (Control.putRegResp r)
/-- Open a control frame as a `RegisterResponse`. -/
def openRegResp (key nonce : ByteArray) (frame : Control.Bytes) : Option Control.RegisterResponse :=
  (openFrame key nonce frame).bind (fun bs => (Control.getRegResp bs).map (·.1))

/-- **`RegisterResponse` round-trips through the channel.** -/
theorem regResp_channel_roundtrip (sk rk nonce : ByteArray) (r : Control.RegisterResponse)
    (hk : sk = rk) {frame : Control.Bytes} (hs : sealRegResp sk nonce r = some frame) :
    openRegResp rk nonce frame = some r := by
  unfold sealRegResp at hs
  have hof := seal_open sk rk nonce (Control.putRegResp r) hk hs
  have hg : Control.getRegResp (Control.putRegResp r) = some (r, []) := by
    have := Control.getRegResp_put r []; rwa [List.append_nil] at this
  simp [openRegResp, hof, hg]

/-- Seal a `MapResponse` (server→node). -/
def sealMapResp (key nonce : ByteArray) (m : Control.MapResponse) : Option Control.Bytes :=
  sealFrame key nonce (putMapResp m)
/-- Open a control frame as a `MapResponse`. -/
def openMapResp (key nonce : ByteArray) (frame : Control.Bytes) : Option Control.MapResponse :=
  (openFrame key nonce frame).bind (fun bs => (getMapResp bs).map (·.1))

/-- **`MapResponse` round-trips through the channel** (the netmap the server
streams to the node arrives intact). -/
theorem mapResp_channel_roundtrip (sk rk nonce : ByteArray) (m : Control.MapResponse)
    (hk : sk = rk) {frame : Control.Bytes} (hs : sealMapResp sk nonce m = some frame) :
    openMapResp rk nonce frame = some m := by
  unfold sealMapResp at hs
  have hof := seal_open sk rk nonce (putMapResp m) hk hs
  have hg : getMapResp (putMapResp m) = some (m, []) := by
    have := getMapResp_put m []; rwa [List.append_nil] at this
  simp [openMapResp, hof, hg]

/-! ## §5  Authenticity — the wire anti-spoof

The confidentiality/authenticity core, the ts2021 analog of
`Disco.disco_authpongframe_genuine`: a control frame that *opens* under a
transport key was genuinely **sealed** under that key. Composed with the
handshake, only a party that completed the Noise IK exchange holding the machine
key ever derives that transport key — so no party lacking it can forge a frame
this channel accepts. -/

/-- **A frame that opens was genuinely sealed (anti-spoof).** If `openFrame`
under a transport key returns a payload, then the frame parsed to some ciphertext
that opened under the key AND was genuinely sealed under it — the functional
shadow of AEAD authenticity (INT-CTXT), via `chacha_open_authentic`. No party
lacking the transport key can fabricate a frame this accepts. -/
theorem channel_frame_genuine (key nonce : ByteArray) (frame payload : Control.Bytes)
    (h : openFrame key nonce frame = some payload) :
    ∃ ct,
      parseFrame frame = some ct ∧
      Crypto.chachaOpen key nonce ByteArray.empty (baOf ct) = some (baOf payload) ∧
      Crypto.chachaSeal key nonce ByteArray.empty (baOf payload) = some (baOf ct) := by
  unfold openFrame at h
  split at h
  · rename_i ct heq
    split at h
    · rename_i pt heq2
      simp only [Option.some.injEq] at h
      have hpt : baOf payload = pt := by rw [← h, baOf_bytesOf]
      refine ⟨ct, heq, ?_, ?_⟩
      · rw [hpt]; exact heq2
      · rw [hpt]
        exact Crypto.Assumptions.chacha_open_authentic key nonce ByteArray.empty (baOf ct) pt heq2
    · simp at h
  · simp at h

/-- **A control message the node accepts was genuinely sealed by the server.**
The typed anti-spoof: if `openRegResp` (server→node) yields a response, the frame
carried a ciphertext genuinely sealed under the node's receive transport key —
which, by the handshake, only the coordination server holding the derived key
could produce. A forged `RegisterResponse` is never accepted. -/
theorem regResp_frame_genuine (key nonce : ByteArray) (frame : Control.Bytes)
    (r : Control.RegisterResponse) (h : openRegResp key nonce frame = some r) :
    ∃ ct payload tail,
      parseFrame frame = some ct ∧
      Crypto.chachaOpen key nonce ByteArray.empty (baOf ct) = some (baOf payload) ∧
      Crypto.chachaSeal key nonce ByteArray.empty (baOf payload) = some (baOf ct) ∧
      Control.getRegResp payload = some (r, tail) := by
  unfold openRegResp at h
  cases ho : openFrame key nonce frame with
  | none => rw [ho] at h; simp at h
  | some payload =>
    rw [ho] at h
    simp only [Option.some_bind, Option.map_eq_some'] at h
    obtain ⟨pr, hgr, hpr⟩ := h
    obtain ⟨ct, hpf, hopen, hseal⟩ := channel_frame_genuine key nonce frame payload ho
    obtain ⟨v, tail⟩ := pr
    refine ⟨ct, payload, tail, hpf, hopen, hseal, ?_⟩
    simp only at hpr
    subst hpr
    exact hgr

/-! ## §6  Handshake-time machine-key authentication (reused)

The initiation seals the node's machine static key inside the first Noise
message (§5.4.2 shape); the coordination server, having derived the same step key
and transcript, recovers it — and no forged machine key is ever accepted. Reuses
`Wireguard.Noise.sealStatic` and its authenticity lemmas directly. -/

/-- Seal the node's machine static public key into the initiation
(`encrypted_static`), under a key derived from the chaining key and the running
transcript hash. Reuses `Wireguard.Noise.sealStatic`. -/
def sealMachineKey (k hash mpub : ByteArray) : Option ByteArray :=
  Noise.sealStatic k hash mpub

/-- **The coordination server recovers the node's genuine machine key.** With the
same derived key and transcript, opening `encrypted_static` yields exactly the
node's machine public key — the machine-key identity is authenticated to the
server. Reuses `Wireguard.Noise.wg_static_key_authenticated`. -/
theorem coord_recovers_machine_key (k hash mpub ct : ByteArray)
    (hseal : sealMachineKey k hash mpub = some ct) :
    Crypto.chachaOpen k Noise.nonce0 hash ct = some mpub :=
  Noise.wg_static_key_authenticated k hash mpub ct hseal

/-- **No forged machine key is accepted (handshake anti-spoof).** The only
ciphertext that opens to a given machine key under this step key/transcript is
the one the genuine node sealed — AEAD forgery-resistance. A server that admits
an initiation only on `chachaOpen … = some mpub` therefore only ever admits a
node that actually holds the shared key material bound to that machine key.
Reuses `Wireguard.Noise.wg_static_key_unforgeable`. -/
theorem machine_key_unforgeable (k hash mpub ct : ByteArray)
    (hopen : Crypto.chachaOpen k Noise.nonce0 hash ct = some mpub) :
    Crypto.chachaSeal k Noise.nonce0 hash mpub = some ct :=
  Noise.wg_static_key_unforgeable k hash mpub ct hopen

/-! ## §7  Residual (named boundary)

What is proven here is the ts2021 **security core**: the Noise-IK handshake as a
transition system with key agreement (`handshake_keys_agree`), the sealed
control-frame round-trip carrying every `Control` message
(`{regReq,mapReq,regResp,mapResp}_channel_roundtrip`), and authenticity
(`channel_frame_genuine`, `regResp_frame_genuine`, `machine_key_unforgeable`) —
sorry-free, over the reused verified `Wireguard.Noise` machinery and the `Crypto`
assumptions.

The residual is the **HTTP transport wiring and live-tailnet interop**: the
`control/controlhttp` `/ts2021` `Upgrade` dance that carries the handshake and
records over a real HTTP connection, and the byte-exact `controlbase` header
offsets, are the wire-framing boundary to pin against a running tailnet. A live
cross-check (the control-plane analog of `wg-live` / `disco-live`) additionally
needs a real coordination server and a tailnet **auth key** (operator-provided).
Those are wire/integration plumbing over this proven core, not new proof
obligations. -/

/-! ## §8  Axiom ledger -/

#print axioms handshake_keys_agree
#print axioms channel_up_needs_handshake
#print axioms channel_established_keys_agree
#print axioms seal_open
#print axioms regReq_channel_roundtrip
#print axioms mapReq_channel_roundtrip
#print axioms regResp_channel_roundtrip
#print axioms mapResp_channel_roundtrip
#print axioms channel_frame_genuine
#print axioms regResp_frame_genuine
#print axioms machine_key_unforgeable

end Control.Channel
