# The `notify` primitive — async-signal AS authority

*(design study, WIP. Read-only census + design + verdict. No core-`Auth` edit here — a
follow-up the design informs.)*

## The one-line thesis

dregg's kernel runs async notification in **at least five separate, real, working
places** — and not one of them expresses *the authority to signal* as a capability. The
seL4→Lean transcription found exactly this gap as the single genuine projection-loss
(`docs/rebuild/AUTHORITY-DIVERGENCE-FINDING.md` §1): the firmament models a Notification
object distinctly from an Endpoint, but a cap to either confers the same dregg authority,
because `Auth` has no `notify` constructor (`Authority/Positional.lean:37`). seL4 splits
them precisely on `SyncSend` vs `Notify` (`SeL4Abstract.lean:182`).

Adding the constructor is a ~9-site mechanical edit (the divergence finding enumerates
them). **The interesting part is not the constructor — it is that `notify` is the
authority the organs already need and silently route around.** This doc shows where, what
the cap algebra on async-signal authority is, and what it unifies. The honest verdict
(§5): this is a *shallow constructor with a deep shadow* — the ctor is trivial, but it
names a primitive that five subsystems each re-implement ungated, and naming it as
authority is what lets the firmament's notification object become faithfully
seL4-grounded and what gives ADOS swarm-coordination a verified async edge. It is a brick,
not because the brick is hard to lay, but because the hole is load-bearing.

---

## Part 1 — The census: where async-signal lives, and the brick-shaped hole

The pattern repeats with eerie regularity. Each subsystem has a real async-delivery
mechanism (a queue, a cursor, a condvar, a `broadcast`, a `Notify`), and gates **who may
read / who may consume** somewhere — but the act of **signalling** (waking, delivering,
emitting) is either ambient (anyone may) or fused into a different authority (ownership,
membership, the `write` edge). Nowhere is "may signal" a thing you hold.

### 1.1 The seL4 Notification object (the modelled-but-unauthority'd case)

`Dregg2/Firmament/SeL4Kernel.lean:236–257` models a `Notification` as a badge-OR
accumulator: `signal n badge := { badge := n.badge ||| badge }`, `wait` reads-and-clears.
Green refinement theorems (`signal_then_wait`, `wait_observes_badge_or`,
`second_wait_is_zero`, `:719–735`) over real Rust
(`sel4/dregg-firmament/src/emulated_kernel.rs:396` `signal` / `:420` `wait`, a
`Condvar`-backed park, `emulated_kernel.rs:228`).

The firmament realizes **both** IPC modalities as distinct kernel objects:
- the synchronous **Endpoint** (`SeL4Kernel.lean:288`, `stageCall`/`recv`/`reply`, a
  rendezvous), and
- the asynchronous **Notification** (`SeL4Kernel.lean:236`, `signal`/`wait`, badge-OR).

But the cap that *names* either is `Cap.endpoint target rights`
(`Authority/Positional.lean:50`) — there is **no `Cap.notification` variant and no
`Auth.notify` right**. So in the authority lattice, holding a cap to a Notification and
holding a cap to an Endpoint are indistinguishable: both confer whatever `[Auth]` rights
the cap lists, and the only IPC-shaped right that is actually load-bearing at the executor
edge is `write` (next section). The kernel's own `ObjectType.notification`
(`SeL4Kernel.lean:379`, retypeable, budget-charged) has no authority shadow.

**Verdict: async-WITHOUT-notify-authority.** The object is real and refined; the
*authority to signal it* is unrepresented. This is the divergence finding's §1, verbatim.

### 1.2 What authority is *actually* load-bearing today (the `write`-collapse)

A sharp fact that frames the whole design. The executor's connectivity edge is
`confersEdgeTo` (`Exec/AuthTurn.lean:34`):

```lean
def confersEdgeTo (t : Label) (cap : Cap) : Bool :=
  (cap == Cap.node t) ||
  (match cap with
   | .endpoint t' rights => (t' == t) && rights.contains Auth.write
   | _ => false)
```

Every cross-cell authority gate (Introduce/delegate `EffectsAuthority.lean:134`,
ExerciseViaCapability `:420`) bottoms out on `rights.contains Auth.write`. And in the
abstract Spec graph, rights are abstracted to `ExecRights = Unit`
(`AuthTurn.lean:11`) — the connectivity skeleton erases *which* right entirely. So today:
**`write` is the only IPC authority the executor distinguishes, and the refinement to the
Spec graph forgets even that.** `read`/`call`/`reply`/`reset`/`grant` exist in the enum
(`Positional.lean:37`) and in tests, but gate no executable effect.

This matters two ways. (1) It means async-signal currently *can only* be expressed as a
`write` (an endpoint send) or as nothing — there is no narrower "may wake but not send a
synchronous message" authority. (2) It means adding `notify` is the **first** authority
that would carve a real distinction the executor enforces beyond `write` — which is either
an argument that the lattice is under-utilized (and `notify` starts fixing that) or that
adding it is premature until effects gate on the existing six. The design (§2) takes the
former position and says why.

### 1.3 The mailbox / CapInbox organ (ownership ≠ signal authority)

`Dregg2/Apps/InboxFactory.lean` models the hosted inbox as a cell with slots
`head_seq`/`tail_seq`/`capacity`/`owner`/`sender_set_root`/`message_root`. The header
states the thesis outright (`InboxFactory.lean:29`):

> `(NO bal value: an inbox message is a capability invocation / notification, not an
> asset move.)`

The two authorization gates (`InboxFactory.lean:183, 191`):
- **deliver** (the signal): `if senders.contains actor ∧ iPending k e < iCap k e` — a
  **membership** check against the `sender_set`, enforced by `SlotCaveat.senderAuthorized`
  (`:104`), proven to BE the caveat (`deliver_matches_senderAuthorized_caveat`, `:359`).
- **consume** (the receive): `if actor = fieldOf ownerField (k.cell e)` — an **ownership
  equality**, the owner slot frozen `Immutable` at birth (`:101`).

The Rust relay (`node/src/relay_service.rs`) delivers by **HTTP polling** — `GET
/relay/drain`, Ed25519-signed; there is no push/wake to the owner; "may drain" is a
signature, not a cap.

**Verdict: async-WITHOUT-notify-authority.** "May deliver a notification into this inbox"
is sender-set membership; "may consume" is owner-equality. Neither is a held capability —
and the data-plane wake (owner learns a message arrived) is a poll, not a signal at all.

### 1.4 The pubsub / channels organ (publisher-slot + ungated broadcast)

`Dregg2/Apps/PubsubFactory.lean`: a topic cell with a shared `head_seq` and per-subscriber
`reader_cursor.<r>` slots. Same disclaimer (`PubsubFactory.lean:24`): "Pubsub is bal-NEUTRAL
(notifications, not value)". The gates (`:157, 166`):
- **publish** (the signal): `if (actor : Int) = psPublisher k e` — equality against a frozen
  `publisher` slot.
- **read**: `if psCursor k e r < psHead k e` — a **cursor-bound predicate**
  (`RelCaveat.fieldLteOther`, `:104`), pure state, no permission object.

The Rust data plane (`node/src/channels_service.rs`) is the most pointed case. New messages
wake subscribers via a Tokio `broadcast` channel:
`tx: broadcast::Sender<(CellId, u64)>` (`channels_service.rs:173`), `push_message` does
`self.tx.send((channel, seq))` **unconditionally** (`:300`), and the SSE endpoint
`messages_stream` (`:1043`) takes **no authorization parameter** (`:1061`) — any client may
`s.channels.subscribe()` (`:1069`) and receive the `(channel, seq)` wake for any topic. The
payload is ciphertext (read-authority is the group-key epoch from commit `72d43dc64`,
enforced in the executor at apply-time, decoupled from delivery), so the *plaintext* is
safe — but the **signal itself** (the wake that "topic X advanced") is broadcast to all
with zero gating.

**Verdict: async-WITHOUT-notify-authority.** Publish-authority is a publisher slot; the
SSE wake is an ungated broadcast; read is cursor state. The "may be signalled that this
topic advanced" authority does not exist.

### 1.5 The WorldEvent dynamics stream (ambient emit, poll-not-push)

`starbridge-v2/src/dynamics.rs:19–59` defines `WorldEvent` — 11 variants
(`CellBorn`, `TurnCommitted`, `TurnRejected`, `BalanceFlowed`, `CapabilityGranted`,
`CapabilityRevoked`, `FieldSet`, `CellSealed`/`Unsealed`/`Destroyed`, `Burned`). Consumers
pull via `since(cursor)` (`:122`): `&self.events[start..]` — an append-only in-memory log
with a monotonic cursor, **poll, not push**. The module says so deliberately (`:10`): "a
plain append-only log with a cursor, not a callback bus".

`emit` (`dynamics.rs:111`) is **unrestricted** — any code may append; any holder of a
`&Dynamics` may `since`/`tail`. There is no authority on producing or consuming the world
event stream.

(Note on the brief's `SurfaceDamaged`: it does **not** exist. The dynamics stream carries
*no* surface-state events at all. Surface geometry/z-order/title are synchronous mutations
on the `Surface` struct, gated by the **window cap** — `Target::Surface { cell }`,
`sel4/dregg-firmament/src/lib.rs:171`; ops `focus`/`raise`/`move`/`resize`
`starbridge-v2/src/shell.rs:365–448` each `authorize(cap)`. A Surface *is* a real
capability — but it signals **nothing** asynchronously; there is no damage event. So the
"surface signals on state-change" idea in the brief is *aspirational*, not extant — and it
is exactly what a `notify`-gated event-driven surface would build, see §2.4.)

**Verdict: async-WITHOUT-notify-authority** (and async-as-poll, not push). Emit is ambient.

### 1.6 The blocklace gossip + the node's `finality_notify` (ambient dissemination)

Consensus dissemination is Cordial-Miners lazy-push gossip
(`blocklace/src/dissemination.rs`, `net/src/gossip.rs` Plumtree). Blocks are Ed25519-signed
(sender identity) and `receive_block` (`blocklace/src/finality.rs:617`) checks signature +
causal closure + equivocation — but **no per-delivery authority**: any federation member
receives blocks from any peer; equivocation evidence propagates ambiently (a peer that
receives both halves detects the conflict locally), exactly as `docs/ORGANS.md` §5
describes. Subscription is membership-scoped (`dissemination.rs` `subscribed_strands`), but
the push is not cap-gated.

And the node already runs a **literal Notification-shaped object**: `finality_notify:
Arc<Notify>` (`node/src/blocklace_sync.rs:107`), `notify_one()` on new blocks (`:329, 363,
1504`), the executor task parking on `.notified()` (`:1860`) "to make the executor truly
quiescent — no polling" (`:105`). This is a Tokio condvar — the *same shape* as the
firmament's `Condvar`-backed seL4 Notification (`emulated_kernel.rs:412` `notify_all`), and
the *same shape* as channels' `broadcast`. Three independent in-process wake mechanisms,
none unified, none authority-gated.

**Verdict: async-WITHOUT-notify-authority.** Gossip dissemination is ambient among members;
the in-process finality wake is an ungated condvar.

### 1.7 The cross-agent `--wake` (an async notify mis-modeled as a sync joint turn)

The integrator census (`[[project-dregg-integrators-one-seam]]`) found all four ADOS-shaped
systems hand-roll a cross-agent signal, and recorded the dregg mapping as "joint turns =
their `--wake` made all-or-nothing." **The code refutes that mapping.** buildr's `bb --wake`
(`~/pug/buildr-private-beta/herdr/src/cli.rs:2189`) enqueues an A2A spool row with `wake:
true` and fires `submit_agent_message_to_pane` — a **non-blocking** post; the recipient
drains on its *next* turn ("no pane injection; recipient hook drains next turn", `:2182`).
The sender does not block; there is no atomic rendezvous.

That is an **asynchronous notify**, not a synchronous joint turn. dregg's `JointTurn`
(`metatheory/Dregg2/JointTurn.lean:105`) is an **equalizer/pullback** of two cells' steps
over a shared turn-id with a conservation balance (CG-2 ⊗ CG-5) — both commit together,
all-or-nothing, *synchronous*. The `Coordination` layer (`Coordination.lean`) is sequenced
MPST, also not async. So the verified metatheory has **no async cross-agent signal at all**
— `--wake` was force-fit onto the one synchronous primitive that exists. The brick is the
async one that's missing.

**Verdict: async-WITHOUT-notify-authority** — and worse, currently mis-modeled as its
synchronous dual.

### Census summary

| # | subsystem | async mechanism (file:line) | "may signal" authority today | hole? |
|---|---|---|---|---|
| 1 | seL4 Notification | badge-OR + Condvar (`SeL4Kernel.lean:250`, `emulated_kernel.rs:396`) | cap rights, but no `notify` ctor → = endpoint | yes |
| 2 | mailbox/CapInbox | sequenced slots; HTTP poll (`InboxFactory.lean:183`, `relay_service.rs`) | sender-set membership | yes |
| 3 | pubsub/channels | cursors + `broadcast` SSE (`PubsubFactory.lean:157`, `channels_service.rs:300`) | publisher slot; broadcast ungated | yes |
| 4 | WorldEvent dynamics | append log + `since(cursor)` (`dynamics.rs:122`) | none (ambient emit) | yes |
| 5 | blocklace gossip | Plumtree push; `finality_notify` (`finality.rs:617`, `blocklace_sync.rs:107`) | membership; condvar ungated | yes |
| 6 | cross-agent `--wake` | spool + non-blocking post (`cli.rs:2189`) | none (and mis-modeled sync) | yes |

**The brick-shaped hole, stated once:** async signalling is real and ubiquitous, but "the
authority to signal" is everywhere *implicit* — folded into ownership (inbox), a frozen
publisher slot (pubsub), a `write` edge (endpoints), or nothing at all (dynamics, gossip,
broadcast, `--wake`). There is no held, attenuable, delegable, revocable *capability to
wake*. That capability is `notify`.

---

## Part 2 — The design: async-signal AS a capability

### 2.0 What `notify` authority *means*

A `notify` capability is the right to **cause a wake / deliver a signal** on a target,
WITHOUT the rights to read its state, send it a synchronous message, or receive its
replies. It is the pure "I may poke you" authority — the attenuated, asynchronous,
fire-and-forget dual of the synchronous endpoint `call`. Holding `notify(target, badge⊑B)`
means: *you may `signal` `target` with a badge in the sub-lattice `B`, and nothing else.*

This is exactly seL4's split. `cap_rights_to_auth` (`SeL4Abstract.lean:182`) confers
`Notify` on the `AllowWrite`-of-a-Notification branch and `SyncSend` on the
`AllowWrite`-of-an-Endpoint branch — *same right bit, different object, different
authority*. dregg today has only `write`; `notify` is the missing async half.

### 2.1 The constructor (the cheap part — do NOT do it here)

```lean
-- Authority/Positional.lean:37  (the follow-up edit)
inductive Auth where
  | read | write | grant | call | reply | reset | control | notify
```

Ripple: ~9 one-line arm additions (enumerated in
`AUTHORITY-DIVERGENCE-FINDING.md` — the felt-encoders ×5, FFI `authCode`, the `Fintype`
`elems` set `Caps.lean:54`, the display arm) + a VK/encoding bump for the felt code. **Zero
proof restructuring**: `attenuate` (`Caps.lean:79`) and `capAuthConferred` are
constructor-generic (they `filter`/return a `List Auth` verbatim), so every
non-amplification proof is invariant. This is the part the design *informs but does not
perform.*

### 2.2 The cap algebra on async-signal authority

The payoff is what `notify` lets the cap algebra *say*. Three operations, all of which the
existing generic machinery already supports — `notify` just gives them async-signal
meaning.

**Attenuate (narrow).** `attenuate keep c` filters the rights list (`Caps.lean:79`). So:
- `attenuate [.notify] c` ⟶ a cap that may *wake* the target but not `write` (send) it —
  the "may poke, may not message" attenuation. This is **new expressivity**: today you
  cannot hand someone the wake-right without the send-right, because both are `write`.
- `attenuate [.read] c` (drop `.notify`) ⟶ "may observe, may not disturb" — the read-only
  watcher who cannot wake.

**Badge-scoping (the sub-lattice refinement).** seL4 badges are the discriminator a signal
carries (scope/membership/fault, `emulated_kernel.rs` comment). The richer cap is not just
`notify` but `notify`-with-a-badge-mask: "may signal, but only badge ⊑ X". Today a `Cap` is
`endpoint target [Auth]` (`Positional.lean:50`) with no payload-scope field. The faithful
design adds an optional **badge mask** to the notify authority — either:
- (a) a new `Cap.notification (target) (rights) (badgeMask : Nat)` constructor (mirrors
  seL4's `NotificationCap oref badge cap_rights`, `SeL4Abstract.lean:149`), where `signal`
  is admissible iff `badge &&& ¬badgeMask == 0` (the signalled bits are within the mask);
  attenuation is `badgeMask₁ ⊆ badgeMask₂` (bit-subset) — the *same* `granted ⊆ held` order
  the firmament `mint` already enforces (`SeL4Kernel.lean:175` `grantOk`), now on the badge
  lattice; or
- (b) keep one `Cap.endpoint` and carry the mask in the rights encoding.

Option (a) is the seL4-faithful one (it makes a Notification cap a *distinct cap shape*, so
α becomes total and the kernel's two object kinds get two cap kinds). The badge mask is a
genuine sub-lattice: `signal` with badge `b` through a cap with mask `m` is the firmament's
`badge := badge ||| (b &&& m)` — and "may wake but only badge X" is `m = {X}`. **This is
the cap-algebra-on-async-signal the brief asks for, and it is the *same* bit-subset order
the mint gate already proves non-amplifying.**

**Delegate / revoke.** Granting `notify` is `recKDelegate` with the attenuated cap; the
non-amplification proof (`attenuate_non_amplifying`, `EffectsAuthority.lean:345`) covers it
for free. Revocation is the existing transitive `CNode.revoke` (`SeL4Kernel.lean:220`,
`revoke_kills_all_doomed`) or the credential `RevocationSet` (`Credential.lean:125`) —
revoking a `notify` cap synchronously darkens the wake-right and its whole derived subtree
(at n=1, immediately — `revoke_chain_synchronous_transitive`). **"This service may wake me
until I revoke" is then a real, revocable capability**, where today it is ambient-broadcast
(channels) or membership (inbox) you cannot cleanly withdraw.

### 2.3 Composition with synchronous Endpoint authority (the sync/async duality)

The lattice gains a clean duality, matching seL4:

| | synchronous | asynchronous |
|---|---|---|
| **send / wake** | `write` (`SyncSend`) | **`notify`** (`Notify`) |
| **receive** | `read` (`Receive`) | (badge `wait` — the dual of `recv`) |
| **request/response** | `call` / `reply` | — (async has no reply) |

`call`/`reply` (`Positional.lean:37`) are the request-response pair on the synchronous
Endpoint (`SeL4Kernel.lean:320` `stageCall` / `:337` `reply`). `notify` is the async
send-with-no-reply: a `signal` never parks and never gets a reply
(`SeL4Kernel.lean:250`). So a held cap can confer:
- `{call, reply}` — full synchronous RPC;
- `{write}` — synchronous send only (fire a message, block, no structured reply);
- `{notify}` — **asynchronous wake only** (the new corner): no block, no message body
  beyond the badge, no reply.

The asymmetry is the point: `notify` has **no receive-dual that confers authority** (a
`wait` consumes your *own* notification — receiving a signal needs no authority over the
signaller; you just read your accumulator). This mirrors seL4 exactly:
`cap_auth_conferred (NotificationCap …)` strips `AllowGrant`/`AllowGrantReply`
(`SeL4Abstract.lean:225`) — a Notification cap **cannot** confer `Grant`/`Call`/`Reply`,
only `Notify` (and `Receive`, the badge-wait). The design should enforce the same: a
`Cap.notification` confers at most `{notify, read}`, never `{grant, call, reply}`. That is
a small, checkable well-formedness lemma — and it is the seL4-faithful shape.

### 2.4 The firmament: an event-driven (notify-gated) Surface

The brief's "Surface that signals on state-change (SurfaceDamaged as a notify)" is
*aspirational* — §1.5 found no surface event exists today. `notify` is precisely what makes
it real and safe. The design: a Surface (already a cap, `Target::Surface { cell }`,
`lib.rs:171`) gains a **notify endpoint** — a Notification object whose `signal` authority
is a `notify` cap over the surface. Then:
- the compositor (or the backing cell) `signal`s the surface's notification on damage
  (geometry/content change), badge = the damage kind;
- a watcher who holds `notify`-watch on the surface `wait`s and repaints — *without*
  holding the surface's mutate-cap (`focus`/`resize`).

This **gates the dynamics stream**: instead of ambient `emit` (`dynamics.rs:111`, anyone),
producing a `SurfaceDamaged` (or any WorldEvent) would require holding `notify` over the
event's subject. A subscriber receives an event iff they hold a `notify`-watch cap over the
subject cell — turning the ungated `since(cursor)` poll (`dynamics.rs:122`) and the ungated
channels `broadcast` (`channels_service.rs:300`) into **cap-gated event delivery**. That is
the unification §3.1 develops: one notify-authority over the three ungated wake mechanisms.

### 2.5 ADOS: notify = the verified async edge between agent loops

The integrator wedge (`[[project-dregg-integrators-one-seam]]`) identified each ADOS-shaped
system's cross-agent signal (buildr `--wake`, builders `recordPhaseComplete`, sig
`swarm-callback`, simbi `AgentRun`) as the one seam dregg should harden. §1.7 showed
`--wake` is an **async notify** that the metatheory currently lacks (it only has the
*synchronous* joint turn). `notify` supplies it:

> A coordinator agent holds `notify(worker_cell, badge ⊑ task-kinds)`; waking the worker is
> a `signal` — cap-gated (the coordinator must hold the wake-right), badge-scoped (it may
> only wake for task kinds in its mask), attenuable (it may sub-delegate "wake for kind K"
> to a sub-coordinator), revocable (the worker withdraws the wake-right and the coordinator
> goes dark). The worker `wait`s on its accumulator and drains on its next loop iteration.

This is buildr's `bb --wake` (`cli.rs:2189`) with the four properties the integrator memo
said dregg adds — *but as the async primitive it actually is*, not force-fit onto the
synchronous joint turn. It composes with joint turns rather than replacing them:
**`notify` is the async coordination edge; `JointTurn` is the synchronous atomic
co-commit.** A swarm uses `notify` to wake idle workers (async, lossy-safe — badge-OR
coalesces duplicate wakes, `wait_observes_badge_or`) and `JointTurn` to atomically hand off
a unit of work (sync, all-or-nothing). **This is the missing primitive that makes verified
swarm-coordination's async layer real** — and it is the answer to the integrator wedge's
async half.

---

## Part 3 — Consequences across the kernel

### 3.1 It unifies the three ungated wake mechanisms under one authority

The census found **three** in-process wake mechanisms with identical shape and zero
gating: the firmament `Condvar` (`emulated_kernel.rs:412`), the channels `broadcast`
(`channels_service.rs:300`), and the node `finality_notify` (`blocklace_sync.rs:107`) —
plus two ambient delivery surfaces (the dynamics `emit`, `dynamics.rs:111`; gossip
dissemination, `finality.rs:617`). `notify` is the single authority over "may wake X". The
unification is not "merge the implementations" (they live at different layers — kernel IPC,
node SSE, consensus) but **one authority vocabulary**: each becomes "the holder of
`notify(subject)` may cause this wake; the holder of the watch may receive it." The seL4
Notification object becomes the *canonical model* the others refine — the firmament already
has it (`SeL4Kernel.lean:236`), it just isn't the thing channels/dynamics/finality route
through. This is the WELD pattern (the capability exists, disconnected): the Notification
object is built; `notify` connects it to the five async sites.

### 3.2 It fits the coalgebra: `notify` is the async modality dual to the synchronous turn

The dregg4 frame (`[[project-dregg4-vision]]`) is "the turn is a guarded comodel; the three
faces (effects ⊕ caveats ⊕ attestation) are the get/put/guard of a lens." The turn is
**synchronous** — a single cell's `step` (`Boundary.F`/`TurnCoalg`), or the synchronous
pullback of two (`JointTurn`). `notify` is the **asynchronous modality** that this frame is
missing:

- A synchronous turn is an *observation that returns* (the lens `get`/`put` produces a next
  state the caller sees). A `signal` is an observation that **does not return** — it
  accumulates into the target's badge and the signaller proceeds (`signal` never parks,
  `SeL4Kernel.lean:250`). That is precisely a **comonadic counit into the target's state**
  with no value back to the signaller — the async co-operation the synchronous comodel
  lacks.
- The badge-OR is **idempotent-coalescing**: N signals before a `wait` collapse to one OR'd
  observation (`wait_observes_badge_or`). This is the defining algebra of an *async* effect
  (order- and multiplicity-insensitive), distinct from the *sequential* turn (every step is
  observed in order). In the dial language: `notify` is a point on a fourth axis —
  **Synchrony** (sync turn ↔ async signal) — orthogonal to Disclosure × Transferability ×
  Agreement. The single-machine principle (`[[project-dregg4-vision]]`) already gave us the
  Agreement axis (n=1 collapses distributed bounds); Synchrony is its sibling (n=1 collapses
  async-signal to immediate — see §3.4).
- Honest scope: this is a *correspondence*, not a built theorem. The dregg4 FOUNDATIONS
  reality-check is blunt that the comonad/comodel names are largely *aspirational* (the real
  spine is a guarded Moore coalgebra + a relational gfp, not a built νF/comodel-morphism).
  So the claim here is calibrated: `notify` is the *natural async modality* the coalgebraic
  frame predicts, and modelling `signal`/`wait` as a coalgebra (state → badge-accumulator,
  the read-and-clear as the structure map) is a buildable companion to `TurnCoalg` — not a
  claim that the comodel already hosts it.

### 3.3 It makes α total on the seL4 IPC authorities (the grounding payoff)

`SeL4Abstract.lean:451`'s relabelling α is faithful+injective on the used 7
(`alpha_injective_on_used`, `:479`) but `Notify ↦ none` (`:459`) is the **one IPC ctor going
to `none`** (`Read`/`Write` go to the memory model, `DeleteDerived` to the revocation
registry, `AAuth` is above-arch — those are *principled* projections per the divergence
finding). Adding `Auth.notify` and mapping `Notify ↦ some .notify` makes α **total on all 7
seL4 IPC authorities** (`Receive, SyncSend, Notify, Reset, Grant, Call, Reply`). Then
`alpha_total_iff_used` (`:473`) extends, `dregg_executor_cap_authority_grounded_in_seL4`
(`:547`) covers the firmament's full IPC + notification authority, and the firmament's
notification object is **faithfully seL4-grounded** rather than 6-of-7-projected. This is
the assurance gain the divergence finding named: the one genuine conflation closed.

### 3.4 Risks / tensions (the honest column)

**Does async break synchronous-turn determinism?** No, if scoped correctly. The signal's
*effect* (badge-OR into the target's accumulator) is a deterministic state write; the
non-determinism is purely *when the target `wait`s*, which is already how the firmament
models it (the blocking is "a scheduling concern; the observable VALUE is this",
`SeL4Kernel.lean:234`). A `signal` should be a turn like any other (it edits the target's
badge field — balance-neutral, like the inbox `deliver`, `InboxFactory.lean:29`); the
*delivery* is the target's own subsequent `wait` turn. So the turn semantics stay
synchronous and deterministic; `notify` adds a *decoupled producer/consumer pair of turns*,
not a non-deterministic interrupt. The discipline: **`signal` and `wait` are each ordinary
turns; the async-ness is the gap between them, not a break in either.**

**Single-machine principle (Houyhnhnm n=1).** At n=1 the async collapses to sync —
exactly as the firmament already realizes: the emulator's single-threaded
`poll_notification` (`emulated_kernel.rs:438`, the inline non-blocking read) has the *same
value semantics* as the cross-thread `wait` (`SeL4Kernel.lean:256` notes this). So
`notify`'s async-delivery gap is a *distributed/concurrent* phenomenon that **collapses to
immediate at n=1** — a signal is observed on the very next pump. This is the Synchrony dial's
n=1 instantiation, consistent with the single-machine principle: you never pay the async
(eventual-delivery) tax on a single-machine workload; `signal`-then-`wait` is immediate.

**Info-flow: the badge-OR is a covert channel.** This is the **one genuine new risk**, and
it is real. A badge-OR accumulator is a classic covert channel: a signaller modulates bits
of the badge, a waiter reads the OR — bandwidth = the badge width, and the OR leaks *that a
signal happened* even across an attenuation that hid the content. seL4 itself treats
notification badges carefully in its info-flow proofs (the `Notify` authority is in the
integrity/confidentiality TCB). The design must:
- treat the **badge mask** as the info-flow scope: `notify(target, mask)` bounds the bits a
  holder can modulate, so attenuation `mask₁ ⊆ mask₂` is also a *bandwidth* attenuation;
- note that "may wake but not read state" (the §2.2 attenuation) is exactly the authority
  that *creates* a one-bit covert channel (the wake itself signals "something happened"), so
  a notify cap is **never** information-free even when stripped of `read`. This is a
  *feature to bound*, not a bug to remove — but it means a `notify` cap must be priced in any
  future noninterference argument (which dregg does not yet have — noninterference is
  explicitly out-of-scope in `SeL4Abstract.lean:41`). **Flagged, not closed.**

---

## Part 4 — The buildable first step

Smallest real increment that turns the design into a theorem, additive and disjoint
(`STAGED-ADDITIVE-THEN-CUTOVER`), touching no live `Auth`:

**Step 0 (this doc).** The census + design. Done.

**Step 1 — the firmament-local `notify` authority + badge-mask cap (a new module, no core
edit).** In a new `Dregg2/Firmament/NotifyAuthority.lean`, beside `SeL4Kernel.lean`:
- define `NotifyCap := { target : ObjId, badgeMask : Nat }` and `signalAdmissible cap badge
  := (badge &&& ~~~cap.badgeMask) == 0` (the bits signalled are within the mask);
- define `signalGated (cap) (n : Notification) (badge)` = `if signalAdmissible cap badge
  then some (n.signal (badge &&& cap.badgeMask)) else none` — the cap-gated wrapper over the
  existing `Notification.signal` (`SeL4Kernel.lean:250`);
- prove, mirroring the existing kernel theorems: (a) **non-amplification** —
  `attenuate`-ing the badge mask (`mask₁ ⊆ mask₂` bit-subset) only narrows what a holder can
  signal (`signalGated` through the narrower cap admits a subset of badges — the badge
  lattice's `grantOk`, reusing `SeL4Kernel.lean:175`'s order); (b) **gate teeth** — a signal
  with a badge bit outside the mask is REFUSED (`none`), both polarities `#guard`'d
  (`mask = {0b001}`, badge `0b100` ⟶ none; badge `0b001` ⟶ some); (c) **the seL4
  well-formedness** — a notification cap confers at most `{notify, read}`, never
  `{grant, call, reply}` (a `decide` lemma, the `SeL4Abstract.lean:225` strip as a dregg
  fact).

This is ~one file, axiom-clean, `#guard`-tested both polarities, reusing the badge-OR and
the `grantOk` order already proven — the same discipline as `SeL4Kernel.lean`. It validates
the **cap algebra on async-signal** (§2.2) as a theorem *before* anyone touches the core
`Auth` inductive. It is the "transfer triangle" of this design: the one validated reference
that the wider weld (gate the channels broadcast, the dynamics emit, the `--wake`) then
amplifies onto.

**Step 2 (the core edit — the follow-up this doc informs, NOT done here).** Add `Auth.notify`
+ the `Cap.notification` variant + the ~9 felt/Fintype/display arms, extend α
(`Notify ↦ some .notify`), re-close `alpha_total_iff_used` / the grounding theorem. Gated on
ember's go (it is a VK/encoding bump).

**Step 3 (the welds).** Route the three ungated wake mechanisms through the authority: the
channels `broadcast` (`channels_service.rs:300`) and the dynamics `emit` (`dynamics.rs:111`)
gated on a `notify`-watch cap over the subject; `--wake` (`cli.rs:2189`) re-expressed as a
cap-gated `signal`. Each is a separate organ-weld wave (`W-organ-*`), reachable from the
shell.

---

## Part 5 — The verdict

**A deep illuminating brick — though the brick itself is a one-line constructor.** The honest
shape:

- *As a constructor*, `notify` is trivial: ~9 mechanical arm-additions, zero proof
  restructuring, a VK bump (`AUTHORITY-DIVERGENCE-FINDING.md` already costed it).

- *As a primitive*, it is the **single async-signal authority that five working subsystems
  each re-implement ungated** — the seL4 Notification (modelled, no authority shadow), the
  inbox (ownership-as-signal), pubsub (publisher-slot + ungated broadcast), the dynamics
  stream (ambient emit), the blocklace (ambient gossip + ungated condvar), and the
  cross-agent `--wake` (an async notify mis-modeled as a synchronous joint turn). That is the
  brick-shaped hole: async is *everywhere*, "may signal" is *nowhere* a capability.

It earns "deep" on four independent counts, each shown above with file:line:
1. **It unifies** the three ungated in-process wake mechanisms + two ambient delivery
   surfaces under one authority (§3.1) — the WELD pattern (the Notification object exists,
   disconnected).
2. **It grounds in seL4** — closes the one genuine IPC conflation, makes α total on all 7
   IPC authorities (§3.3), the divergence finding's named payoff.
3. **It fits the coalgebra** as the async modality dual to the synchronous turn — a fourth
   *Synchrony* dial, sibling to the single-machine *Agreement* dial (§3.2), calibrated as a
   correspondence + a buildable companion coalgebra, not an overclaimed existing object.
4. **It enables ADOS-async** — supplies the verified async cross-agent edge the integrator
   wedge identified, as the primitive `--wake` actually is, composing with (not replacing)
   the synchronous joint turn (§2.5, §1.7).

The one genuine new cost is **info-flow**: a badge-OR is a covert channel, and "may wake but
not read" is exactly the authority that creates a one-bit leak (§3.4). That is a bound to
price (and dregg has no noninterference argument yet), not a reason to withhold the brick —
but it is the tension to name in the same breath.

**Recommendation:** build Step 1 (the firmament-local notify-authority + badge-mask cap, one
axiom-clean module) as the validated reference — it makes the cap-algebra-on-async-signal a
theorem without touching the core. Hold Step 2 (the `Auth.notify` core edit + α-totalization)
for ember's go, since it is a VK/encoding bump. The design above is what that go would
execute.

---

### Appendix — the load-bearing file:line index

- divergence finding (the §1 conflation, the ~9-site ripple): `docs/rebuild/AUTHORITY-DIVERGENCE-FINDING.md`
- the modelled-but-unauthority'd Notification: `metatheory/Dregg2/Firmament/SeL4Kernel.lean:236–257`, `:719–735`; Rust `sel4/dregg-firmament/src/emulated_kernel.rs:396` (signal) / `:420` (wait) / `:412` (`notify_all`) / `:228` (`Condvar`)
- the seL4 transcription + α: `metatheory/Dregg2/Firmament/SeL4Abstract.lean:182` (SyncSend vs Notify), `:451` (α), `:459` (`Notify ↦ none`), `:473` (`alpha_total_iff_used`), `:547` (grounding)
- the `Auth` enum + Cap: `metatheory/Dregg2/Authority/Positional.lean:37`, `:49`
- the `write`-collapse gate: `metatheory/Dregg2/Exec/AuthTurn.lean:34` (`confersEdgeTo`), `:11` (`ExecRights = Unit`)
- attenuate (generic): `metatheory/Dregg2/Exec/Caps.lean:79`; `Fintype` elems `:54`; cross-cell gates `metatheory/Dregg2/Exec/EffectsAuthority.lean:134, 345, 420`
- mailbox: `metatheory/Dregg2/Apps/InboxFactory.lean:29` (notification-not-value), `:183` (deliver gate), `:191` (consume gate), `:359` (gate-IS-caveat); Rust `node/src/relay_service.rs`
- pubsub/channels: `metatheory/Dregg2/Apps/PubsubFactory.lean:24, 157, 166`; Rust `node/src/channels_service.rs:173` (broadcast), `:300` (ungated send), `:1061` (no-auth SSE)
- dynamics: `starbridge-v2/src/dynamics.rs:19` (WorldEvent), `:111` (ambient emit), `:122` (`since`); Surface `sel4/dregg-firmament/src/lib.rs:171`, shell ops `starbridge-v2/src/shell.rs:365`
- blocklace: `blocklace/src/finality.rs:617` (`receive_block`), `blocklace/src/dissemination.rs`; node wake `node/src/blocklace_sync.rs:107, 329, 1860`
- joint turn / coordination / `--wake`: `metatheory/Dregg2/JointTurn.lean:105`, `metatheory/Dregg2/Coordination.lean`, `~/pug/buildr-private-beta/herdr/src/cli.rs:2189`
- the comodel/dial frame + single-machine principle: `[[project-dregg4-vision]]`; the organ welds: `docs/ORGANS.md`; the integrator wedge: `[[project-dregg-integrators-one-seam]]`
