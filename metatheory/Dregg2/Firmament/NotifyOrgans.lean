/-
# Dregg2.Firmament.NotifyOrgans — the `notify` CASCADE across the organs (the WELD, STEP-3 Lean).

This module is the **WELD** the `notify` primitive was built for (`.docs-history-noclaude/NOTIFY-PRIMITIVE.md` §3.1,
`.docs-history-noclaude/NOTIFY-CASCADE.md` §1e/§5): the census found **five subsystems** that each re-implement
async-signal UNGATED — the seL4 `Notification` (modelled, no authority shadow), the mailbox/CapInbox
(`deliver` = sender-set MEMBERSHIP), pubsub/channels (`publish` = a frozen publisher SLOT + an UNGATED
`broadcast`), the WorldEvent dynamics (`emit` = AMBIENT), the blocklace `finality_notify` (an in-process
condvar). Each is, structurally, **an instance of the ONE `notify` authority** — *a publisher signalling
subscribers IS a notify cap; a mailbox `deliver` IS a notify; an event `emit` IS a notify* — currently
ungated only because, until Step 1, there was no notify cap to hold. This module models that:
the (ungated) wake becomes `signalGated` under a `NotifyCap`, **inheriting the non-amplification** the
`NotifyAuthority` keystones already prove.

## We WELD — we do NOT reinvent (the capability EXISTS, disconnected)

Per the MINTED `THE WELD METHOD` (census first — the capability usually already EXISTS, disconnected;
welding beats building): everything load-bearing already exists and is REUSED verbatim.

  * `Dregg2.Firmament.NotifyAuthority` — `NotifyCap{target,rights,badgeMask}`, `signalGated`,
    `attenuateNotify`, and the keystone `signalAdmissible_attenuate_no_amplify` (+ `signalGated_commits_…`
    / `signalGated_refuses_…`, `badgeWithinMask_mono`). We `import` it and **reuse its body unchanged** —
    every organ's wake is one of ITS `signalGated`s; every organ's non-amplification IS its keystone.
  * `Dregg2.Firmament.SeL4Kernel.Notification` — the badge-OR accumulator (the canonical model §3.1 says
    "the others refine"). Each organ's wake accumulator is modelled as THIS one object (a pubsub head, an
    inbox head, an event log — all badge-OR-shaped), so `signalGated` wraps the SAME `Notification.signal`.
  * The existing organ Lean models — `Dregg2.Apps.PubsubFactory` (`pubsubPublish`, the frozen-`publisher`
    gate `:157`) and `Dregg2.Apps.InboxFactory` (`inboxDeliver`, the sender-set MEMBERSHIP gate `:183`) —
    are the things whose wake we re-express. We MODEL the weld (the publish/deliver authority, re-routed
    through a `NotifyCap`); we do not edit their bodies (a sibling lane owns Apps).

So the WELD is structural: each organ's "may signal" — today a publisher-slot equality / a sender-set
membership / nothing at all — becomes "hold a `NotifyCap` over the organ's accumulator", and the
attenuation/non-amplification is INHERITED, not re-proved. The Notification object existed, disconnected
from a cap; here each organ's wake IS a notify cap.

## What is modelled, per organ (Lean-modelled vs Rust-only-later)

  | organ | Lean model exists? | what this file models |
  |---|---|---|
  | **PUBSUB / channels** | YES (`Apps/PubsubFactory.lean`) | publish-wake as `signalGated` (§1): a publisher holds a `NotifyCap` to the topic's Notification accumulator; publishing a badge is `signalGated`; an ATTENUATED subscriber cap = "may receive badge X only"; a publisher can't signal a badge it doesn't hold + an attenuated subscriber receives a SUBSET. |
  | **MAILBOX / CapInbox** | YES (`Apps/InboxFactory.lean`) | `deliver`-wake as `signalGated` (§2) under the SENDER's notify cap (replacing the frozen sender-set membership); the sender can't deliver a badge it doesn't hold; consume stays owner (unmodelled — it is the receive side, needs no authority, §2.3). |
  | **WorldEvent dynamics** | NO (Rust-only, `starbridge-v2/src/dynamics.rs:111`) | the AUTHORITY SHAPE (§3): the ambient `emit` becomes `signalGated` under a `NotifyCap` over the event's subject; a producer can't emit a subject-badge it doesn't hold. The Rust `emit`-gating weld is a LATER wave (`W-organ-emit`). |
  | **blocklace `finality_notify`** | NO (Rust-only, `node/src/blocklace_sync.rs:107`) | in-process condvar — no cross-boundary cap needed (§3.1: "modelled as the canonical Notification the others refine"); it IS `Notification`, so it is already the §0 canonical object. No new model; named as the canonical wake. |

## THE UNIFICATION THEOREM (§4)

The point of the whole cascade: the ungated wakes, modelled as `signalGated`, **ALL inherit the notify
non-amplification** — i.e. they are ONE notify authority. `organ_wakes_are_one_notify_authority` quantifies
over ANY organ wake (any `(cap, accumulator, badge)`) and shows every one obeys the SAME three laws
(commit-iff-admissible, fail-closed-refuse, attenuation-only-shrinks) — so "pubsub publish", "inbox
deliver", and "event emit" are not three authorities but three *instances* of `NotifyAuthority`'s one.
Then the per-organ corollaries (`pubsub_publish_no_amplify`, `inbox_deliver_no_amplify`,
`event_emit_no_amplify`) are each ONE LINE off the unification — the weld made visible.

## Discipline

NON-VACUITY both polarities (`#guard` teeth that BITE per organ): a publisher commits a held topic-badge
and REFUSES an unheld one; an attenuated subscriber receives a strict SUBSET; a sender delivers a held
badge and REFUSES an unheld one; an event producer emits a held subject and REFUSES an unheld one.

Axiom-clean (`#assert_all_clean` at the close). `lake build` green
(LOCAL). WIDE-SAFE: NO core `Auth`, NO circuit, NO felt-encoder, NO VK — runs on the committed Step-1
`NotifyAuthority` + the existing organ models. Imports `NotifyAuthority` (reuses its body, does not edit
it); does NOT edit Apps / the kernel / `SwarmSignal` / any Metatheory/*.
-/
import Dregg2.Firmament.NotifyAuthority
import Dregg2.Tactics

namespace Dregg2.Firmament.NotifyOrgans

open Dregg2.Firmament.SeL4Kernel (Notification ObjId)
open Dregg2.Exec.CapTPConcrete (AuthReq)
open Dregg2.Firmament.NotifyAuthority (NotifyCap signalGated maskNarrowerOrEqual badgeWithinMask
  signalAdmissible_attenuate_no_amplify signalGated_commits_of_admissible
  signalGated_refuses_of_inadmissible badgeWithinMask_mono)

/-! ## §0 — The shared organ-wake abstraction (the canonical Notification the others refine).

§3.1 of the design: the seL4 `Notification` object is the *canonical model* the other wake mechanisms
refine — the firmament already has it (`SeL4Kernel.lean:236`); the organs just don't route through it.
An ORGAN WAKE is therefore exactly a triple `(NotifyCap, Notification, badge)`: the held cap (who may
wake), the badge-OR accumulator (the organ's wake surface — a pubsub head, an inbox head, an event log),
and the badge (the topic / sender / event-subject discriminator). Every organ below instantiates THIS
triple, and its wake is `signalGated` over it. The blocklace `finality_notify` (`blocklace_sync.lean`
n/a — Rust `Arc<Notify>`) IS this `Notification` directly (an in-process condvar of the same shape),
so it needs no separate model — it is the canonical object, named. -/

/-- **`OrganWake`** — a uniform view of any organ's async-signal site: the held `NotifyCap` (the "may
wake" authority), the `Notification` badge-OR accumulator (the wake surface — the same object for every
organ, §3.1), and the conferred badge (the topic/sender/subject discriminator). The three organs below
are each an `OrganWake`; the unification theorem (§4) is a fact about ALL of them. -/
structure OrganWake where
  /-- The held capability to wake this organ's accumulator (the §2.0 "may poke" authority). -/
  cap : NotifyCap
  /-- The organ's badge-OR wake surface (the canonical `Notification` the others refine, §3.1). -/
  accum : Notification
  /-- The badge this wake carries (topic-kind / sender-tag / event-subject). -/
  badge : Nat
  deriving Repr

/-- **`OrganWake.fire ow`** — the organ's wake, executed: `signalGated` over the held cap and the
accumulator. This is the SINGLE definition every organ's wake reduces to — the WELD made one function.
Commits (`some`, OR'ing the masked badge) iff the cap admits the badge; refuses (`none`) otherwise. -/
def OrganWake.fire (ow : OrganWake) : Option Notification := signalGated ow.cap ow.accum ow.badge

/-! ## §1 — PUBSUB / channels: publish-wake AS a notify (the most pointed ungated case).

`Apps/PubsubFactory.lean:157` gates `pubsubPublish` on `(actor : Int) = psPublisher k e` — a frozen
publisher SLOT equality; the Rust `channels_service.rs:300` `broadcast.send` is UNGATED, the SSE
(`:1061`) takes NO authorization. The WELD: a publisher HOLDS a `NotifyCap` to the topic's Notification
accumulator; publishing topic-kind `b` is `signalGated` — it commits iff `b` is within the publisher's
held topic-mask. An ATTENUATED subscriber/sub-publisher cap = "may publish/receive badge X only"
(`attenuateNotify`), and the keystone gives: the attenuated cap admits a SUBSET (a restricted publisher
cannot signal a topic-kind the full publisher could not). The frozen `publisher` slot becomes a held,
attenuable, delegable cap — the design's §5 PubsubFactory feature. -/

/-- **`pubsubTopicCap publisher topicMask`** — the publisher's held notify cap over a pubsub topic
(object `publisher`'s reach is the topic's badge-OR accumulator, scoped to topic-kinds within
`topicMask`). This is the held replacement for the frozen `psPublisher` slot: "may wake subscribers of
this topic, for topic-kinds ⊑ `topicMask`". The `rights` ride the existing `AuthReq`/`grantOk`. -/
def pubsubTopicCap (topic : ObjId) (rights : AuthReq) (topicMask : Nat) : NotifyCap :=
  { target := topic, rights := rights, badgeMask := topicMask }

/-- **`pubsubPublishGated cap accum topicKind`** — the publish-wake as a notify: publishing
`topicKind` into the topic's accumulator is `signalGated` under the publisher's cap. Commits (OR's the
topic-kind into the accumulator, waking every subscriber) iff `topicKind ⊑ topicMask`; refuses
otherwise. The cap-gated form of the UNGATED `channels_service.rs:300` `broadcast.send`. -/
def pubsubPublishGated (cap : NotifyCap) (accum : Notification) (topicKind : Nat) : Option Notification :=
  signalGated cap accum topicKind

/-- **`subscriberWatchCap` — an ATTENUATED subscriber cap, "may receive badge X only".** A
sub-publisher (or a restricted subscriber-relay) is handed an attenuated topic cap via `attenuateNotify`:
narrower rights + a narrower topic-mask (`narrowerKinds ⊆ topicMask`). `none` if it would widen on
either axis — the design's "a subscriber receives a SUBSET" as the cap-algebra attenuation. -/
def subscriberWatchCap (cap : NotifyCap) (narrowerRights : AuthReq) (narrowerKinds : Nat) :
    Option NotifyCap :=
  cap.attenuateNotify narrowerRights narrowerKinds

/-- **PUBSUB WELD — a publisher cannot signal a topic-kind it does NOT hold** (the negative gate, the
ungated-`broadcast`-now-gated tooth): if `topicKind` is outside the held topic-mask, `pubsubPublishGated`
REFUSES (`none`). The frozen-publisher-slot-replacement bites: holding a topic cap is necessary AND its
mask bounds which kinds you may publish. This is `signalGated_refuses_of_inadmissible`, on the pubsub
accumulator — the weld is that this organ's publish IS that gate. -/
theorem pubsubPublish_refuses_unheld_kind
    (cap : NotifyCap) (accum : Notification) (topicKind : Nat)
    (hunheld : cap.signalAdmissible topicKind = false) :
    pubsubPublishGated cap accum topicKind = none :=
  signalGated_refuses_of_inadmissible cap accum topicKind hunheld

/-- **PUBSUB WELD — a held topic-kind publishes** (the positive gate): a topic-kind within the held mask
COMMITS, OR'ing exactly that kind into the topic's accumulator (waking subscribers). The non-vacuity
partner of the refusal. -/
theorem pubsubPublish_commits_held_kind
    (cap : NotifyCap) (accum : Notification) (topicKind : Nat)
    (hheld : cap.signalAdmissible topicKind = true) :
    pubsubPublishGated cap accum topicKind = some (accum.signal topicKind) :=
  signalGated_commits_of_admissible cap accum topicKind hheld

/-- **PUBSUB WELD — an ATTENUATED subscriber/sub-publisher receives a SUBSET.** A cap attenuated to
`narrowerKinds` admits a SUBSET of the topic-kinds the full publisher admits — every kind the restricted
cap can publish, the full publisher could too (never the reverse). "May receive badge X only" is a
genuine restriction, inherited from `signalAdmissible_attenuate_no_amplify`. The WELD: the pubsub
publisher-attenuation IS the notify non-amplification. -/
theorem pubsubSubscriber_receives_subset
    (cap : NotifyCap) (narrowerRights : AuthReq) (narrowerKinds : Nat) (sub : NotifyCap)
    (hsub : subscriberWatchCap cap narrowerRights narrowerKinds = some sub)
    (topicKind : Nat) (hadm : sub.signalAdmissible topicKind = true) :
    cap.signalAdmissible topicKind = true :=
  signalAdmissible_attenuate_no_amplify cap narrowerRights narrowerKinds sub hsub topicKind hadm

/-! ## §2 — MAILBOX / CapInbox: deliver-wake AS a notify (sender's cap, not the frozen sender-set).

`Apps/InboxFactory.lean:183` gates `inboxDeliver` on `senders.contains actor` — a sender-set MEMBERSHIP
check (a frozen list). The header (`InboxFactory.lean:29`) states the thesis: "an inbox message is a
capability invocation / **notification**, not an asset move". The WELD: a sender holds a `NotifyCap` over
the inbox's Notification accumulator (the deliver surface); delivering a message tagged `senderTag` is
`signalGated` under THAT cap — replacing the frozen sender-set membership with a held, attenuable,
revocable deliver-right. The sender can't deliver a tag it doesn't hold. Consume stays owner-only (the
receive side — it needs no authority over the signaller, §2.3 — so it is NOT modelled here as a wake). -/

/-- **`inboxSenderCap inbox rights senderMask`** — a sender's held notify cap over an inbox (object
`inbox`'s accumulator, scoped to sender-tags within `senderMask`). The held replacement for sender-set
membership: "may deliver into this inbox, for tags ⊑ `senderMask`". -/
def inboxSenderCap (inbox : ObjId) (rights : AuthReq) (senderMask : Nat) : NotifyCap :=
  { target := inbox, rights := rights, badgeMask := senderMask }

/-- **`inboxDeliverGated cap accum senderTag`** — the deliver-wake as a notify: delivering a message
tagged `senderTag` into the inbox's accumulator is `signalGated` under the sender's cap. Commits (OR's
the tag in, signalling the owner a message arrived) iff `senderTag ⊑ senderMask`; refuses otherwise.
The cap-gated form of the sender-set-membership `inboxDeliver` gate. (The capacity leg
`iPending < iCap` is the orthogonal relational caveat — preserved on the Apps side, not the wake
authority this models.) -/
def inboxDeliverGated (cap : NotifyCap) (accum : Notification) (senderTag : Nat) : Option Notification :=
  signalGated cap accum senderTag

/-- **MAILBOX WELD — a sender cannot deliver a tag it does NOT hold** (the membership-replacement tooth):
a sender-tag outside the held sender-mask REFUSES (`none`) — holding the inbox cap is necessary, and its
mask bounds which deliveries you may make. This replaces "is `actor` in the frozen `sender_set`?" with
"does the sender hold a cap admitting this tag?". `signalGated_refuses_of_inadmissible`, on the inbox
accumulator. -/
theorem inboxDeliver_refuses_unheld_tag
    (cap : NotifyCap) (accum : Notification) (senderTag : Nat)
    (hunheld : cap.signalAdmissible senderTag = false) :
    inboxDeliverGated cap accum senderTag = none :=
  signalGated_refuses_of_inadmissible cap accum senderTag hunheld

/-- **MAILBOX WELD — a held tag delivers** (the positive gate): a sender-tag within the held mask
COMMITS, OR'ing the tag into the inbox accumulator (the owner's wake). Non-vacuity partner. -/
theorem inboxDeliver_commits_held_tag
    (cap : NotifyCap) (accum : Notification) (senderTag : Nat)
    (hheld : cap.signalAdmissible senderTag = true) :
    inboxDeliverGated cap accum senderTag = some (accum.signal senderTag) :=
  signalGated_commits_of_admissible cap accum senderTag hheld

/-- **MAILBOX WELD — an ATTENUATED sender delivers a SUBSET.** A sender cap attenuated to `narrowerMask`
admits a SUBSET of the tags the full sender could deliver — a sub-delegated deliver-right ("forward into
this inbox, tag K only") is a genuine restriction. Inherited from the keystone. The WELD: the inbox
deliver-attenuation IS the notify non-amplification. -/
theorem inboxSender_delivers_subset
    (cap : NotifyCap) (narrowerRights : AuthReq) (narrowerMask : Nat) (sub : NotifyCap)
    (hsub : cap.attenuateNotify narrowerRights narrowerMask = some sub)
    (senderTag : Nat) (hadm : sub.signalAdmissible senderTag = true) :
    cap.signalAdmissible senderTag = true :=
  signalAdmissible_attenuate_no_amplify cap narrowerRights narrowerMask sub hsub senderTag hadm

/-! ## §3 — WorldEvent dynamics: the AMBIENT emit AS a notify (Rust-only — the authority SHAPE).

`starbridge-v2/src/dynamics.rs:111` `emit` is UNRESTRICTED — any code with `&mut Dynamics` may append a
`WorldEvent`; `since(cursor)` (`:122`) is an ungated poll. There is NO Lean model of `Dynamics` (it is a
Rust append-log), so we model the AUTHORITY SHAPE the weld would impose (per the cascade plan: "producing
an event requires holding `notify` over the event's subject"): emitting an event about subject-cell
`subject` is `signalGated` under a `NotifyCap` whose target is the subject and whose badge is the
event-kind. The Rust `emit`-gating (route `dynamics.rs:111` through a held subject-cap) is a LATER wave
(`W-organ-emit`); here we pin that the AUTHORITY is the same `notify` one — so when the Rust weld lands,
its non-amplification is ALREADY a theorem. -/

/-- **`eventSubjectCap subject rights kindMask`** — a producer's held notify cap over a WorldEvent
subject (object `subject`'s event surface, scoped to event-kinds within `kindMask`). The held
replacement for AMBIENT `emit`: "may emit events about this subject, for kinds ⊑ `kindMask`" — e.g. the
backing cell of a surface may emit `FieldSet`/`CellSealed` about itself, not about a cell it lacks the
cap for. -/
def eventSubjectCap (subject : ObjId) (rights : AuthReq) (kindMask : Nat) : NotifyCap :=
  { target := subject, rights := rights, badgeMask := kindMask }

/-- **`eventEmitGated cap accum eventKind`** — the emit as a notify: emitting an event of kind
`eventKind` about the subject is `signalGated` under the producer's subject-cap. Commits iff
`eventKind ⊑ kindMask`; refuses otherwise. The cap-gated form of the AMBIENT `dynamics.rs:111` emit.
(The subject's event surface is modelled as a `Notification` — the §3.1 canonical object the dynamics
stream would refine; the Rust `Vec<WorldEvent>` append is the un-modelled side, the `W-organ-emit`
wave.) -/
def eventEmitGated (cap : NotifyCap) (accum : Notification) (eventKind : Nat) : Option Notification :=
  signalGated cap accum eventKind

/-- **DYNAMICS WELD — a producer cannot emit an event-kind it does NOT hold** (the ambient-emit-now-gated
tooth): an event-kind outside the held subject-mask REFUSES (`none`). The unrestricted `emit` becomes
cap-authorized: you may emit only event-kinds your subject-cap admits. `signalGated_refuses_of_inadmissible`,
on the event surface. -/
theorem eventEmit_refuses_unheld_kind
    (cap : NotifyCap) (accum : Notification) (eventKind : Nat)
    (hunheld : cap.signalAdmissible eventKind = false) :
    eventEmitGated cap accum eventKind = none :=
  signalGated_refuses_of_inadmissible cap accum eventKind hunheld

/-- **DYNAMICS WELD — a held event-kind emits** (the positive gate): an event-kind within the held mask
COMMITS, OR'ing the kind into the subject's event surface. Non-vacuity partner. -/
theorem eventEmit_commits_held_kind
    (cap : NotifyCap) (accum : Notification) (eventKind : Nat)
    (hheld : cap.signalAdmissible eventKind = true) :
    eventEmitGated cap accum eventKind = some (accum.signal eventKind) :=
  signalGated_commits_of_admissible cap accum eventKind hheld

/-! ## §4 — THE UNIFICATION THEOREM: the ungated wakes are ONE notify authority.

The payoff of the whole cascade. Each organ above defined its wake as a `signalGated` over a triple
`(cap, accumulator, badge)` — i.e. as an `OrganWake.fire`. The unification: EVERY organ wake obeys the
SAME three laws (commit-iff-admissible, fail-closed-refuse, attenuation-only-shrinks), because each IS
the same `NotifyAuthority.signalGated`. So "pubsub publish", "inbox deliver", and "event emit" are not
three authorities — they are three INSTANCES of the one `notify` authority. The per-organ corollaries are
each ONE LINE off this theorem (`pubsubPublishGated`/`inboxDeliverGated`/`eventEmitGated` are all `fire`
definitionally), so the weld is structural, not a coincidence proved three times. -/

/-- **THE UNIFICATION THEOREM — every organ wake IS the one notify authority.** For ANY `OrganWake ow`
(any organ's `(cap, accumulator, badge)`), its wake obeys the three notify laws:
  1. **commit-iff-admissible** — `ow.fire` is `some` exactly when the cap admits the badge (and then
     OR's exactly the badge), and `none` exactly when it does not (fail-closed);
  2. **attenuation-only-shrinks** — for any attenuation of `ow.cap` to `sub`, every badge `sub` admits,
     `ow.cap` admits too (the non-amplification, inherited).
Because pubsub/inbox/dynamics each defined their wake AS an `OrganWake.fire`, this ONE theorem covers all
three — they are ONE authority. -/
theorem organ_wakes_are_one_notify_authority (ow : OrganWake) :
    -- (1) commit-iff-admissible (both directions), OR'ing exactly the badge when it commits:
    (ow.cap.signalAdmissible ow.badge = true → ow.fire = some (ow.accum.signal ow.badge))
      ∧ (ow.cap.signalAdmissible ow.badge = false → ow.fire = none)
    -- (2) attenuation only shrinks the admissible badge set (the non-amplification, inherited):
      ∧ (∀ (nr : AuthReq) (nm : Nat) (sub : NotifyCap),
           ow.cap.attenuateNotify nr nm = some sub →
           ∀ b, sub.signalAdmissible b = true → ow.cap.signalAdmissible b = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hadm
    exact signalGated_commits_of_admissible ow.cap ow.accum ow.badge hadm
  · intro hinadm
    exact signalGated_refuses_of_inadmissible ow.cap ow.accum ow.badge hinadm
  · intro nr nm sub hsub b hb
    exact signalAdmissible_attenuate_no_amplify ow.cap nr nm sub hsub b hb

/-- **The non-amplification leg, isolated** — for ANY organ wake, attenuating its cap only SHRINKS what
it may signal. The single fact that makes "the ungated wakes inherit the non-amplification" precise: it
holds uniformly over every `OrganWake`, hence over pubsub publish, inbox deliver, AND event emit at once.
-/
theorem organ_wake_attenuation_no_amplify
    (ow : OrganWake) (nr : AuthReq) (nm : Nat) (sub : NotifyCap)
    (hsub : ow.cap.attenuateNotify nr nm = some sub)
    (b : Nat) (hb : sub.signalAdmissible b = true) :
    ow.cap.signalAdmissible b = true :=
  signalAdmissible_attenuate_no_amplify ow.cap nr nm sub hsub b hb

/-! ### The per-organ corollaries — each ONE LINE off the unification (the weld, made visible).

Because `pubsubPublishGated`, `inboxDeliverGated`, and `eventEmitGated` are all `signalGated` (= the body
of `OrganWake.fire`), each organ's non-amplification is the SAME theorem viewed through its own cap. These
are the "they are ONE authority" claim, organ by organ. -/

/-- **PUBSUB is the notify authority** — the pubsub publisher-attenuation non-amplification, as the
unification specialised to a topic cap (definitionally `pubsubPublishGated = fire`). -/
theorem pubsub_publish_no_amplify
    (cap : NotifyCap) (nr : AuthReq) (nm : Nat) (sub : NotifyCap)
    (hsub : cap.attenuateNotify nr nm = some sub)
    (b : Nat) (hb : sub.signalAdmissible b = true) :
    cap.signalAdmissible b = true :=
  organ_wake_attenuation_no_amplify ⟨cap, Notification.empty, 0⟩ nr nm sub hsub b hb

/-- **MAILBOX is the notify authority** — the inbox deliver-attenuation non-amplification, as the
unification specialised to an inbox sender cap. -/
theorem inbox_deliver_no_amplify
    (cap : NotifyCap) (nr : AuthReq) (nm : Nat) (sub : NotifyCap)
    (hsub : cap.attenuateNotify nr nm = some sub)
    (b : Nat) (hb : sub.signalAdmissible b = true) :
    cap.signalAdmissible b = true :=
  organ_wake_attenuation_no_amplify ⟨cap, Notification.empty, 0⟩ nr nm sub hsub b hb

/-- **DYNAMICS is the notify authority** — the WorldEvent emit-attenuation non-amplification, as the
unification specialised to an event-subject cap. (Rust-modelled-later, but the authority is ALREADY one.)
-/
theorem event_emit_no_amplify
    (cap : NotifyCap) (nr : AuthReq) (nm : Nat) (sub : NotifyCap)
    (hsub : cap.attenuateNotify nr nm = some sub)
    (b : Nat) (hb : sub.signalAdmissible b = true) :
    cap.signalAdmissible b = true :=
  organ_wake_attenuation_no_amplify ⟨cap, Notification.empty, 0⟩ nr nm sub hsub b hb

/-- **THE WELD, STATED ONCE — the three organ wakes are definitionally the ONE `signalGated`.** Pubsub
publish, inbox deliver, and event emit, on the SAME cap / accumulator / badge, are the IDENTICAL
operation (each is `signalGated cap accum badge`). This `rfl` is the structural heart of the weld: there
is no "pubsub authority" vs "inbox authority" vs "dynamics authority" to reconcile — there is one
`signalGated`, three names. -/
theorem organ_wakes_are_definitionally_one
    (cap : NotifyCap) (accum : Notification) (badge : Nat) :
    pubsubPublishGated cap accum badge = inboxDeliverGated cap accum badge
      ∧ inboxDeliverGated cap accum badge = eventEmitGated cap accum badge
      ∧ eventEmitGated cap accum badge = (OrganWake.fire ⟨cap, accum, badge⟩) := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## §5 — NON-VACUITY TEETH (`#guard`): per organ, both polarities BITE on concrete badges.

Each organ's gate bites on a concrete cap: mask `0b101` (two kinds held) admits `0b001`/`0b100`, REFUSES
`0b010`; the attenuated `0b101 → 0b001` admits strictly fewer. Same teeth as `NotifyAuthority` §5, now
worn by the pubsub publisher, the inbox sender, and the event producer — witnessing each is the one
authority. -/

section Witnesses

/-- A concrete topic cap: topic object `7`, signature rights, topic-mask `0b101` (publish kinds `0b001`,
`0b100`). -/
def egTopicCap : NotifyCap := { target := 7, rights := .signature, badgeMask := 0b101 }
/-- A concrete inbox sender cap: inbox `8`, signature rights, sender-mask `0b101`. -/
def egInboxCap : NotifyCap := { target := 8, rights := .signature, badgeMask := 0b101 }
/-- A concrete event subject cap: subject `9`, signature rights, kind-mask `0b101`. -/
def egSubjectCap : NotifyCap := { target := 9, rights := .signature, badgeMask := 0b101 }

/-! ### PUBSUB teeth — publish a held kind (COMMITS), refuse an unheld kind, attenuated ⇒ SUBSET. -/

-- COMMITS: topic-kind `0b001` is within the mask ⇒ publish `some`, OR'ing `0b001` (subscribers woken).
#guard (pubsubPublishGated egTopicCap Notification.empty 0b001).isSome
#guard pubsubPublishGated egTopicCap Notification.empty 0b001 == some (Notification.empty.signal 0b001)
-- COMMITS: the OTHER held kind `0b100`.
#guard (pubsubPublishGated egTopicCap Notification.empty 0b100).isSome
-- REFUSES: kind `0b010` not in the topic-mask ⇒ `none` (the ungated broadcast, now fail-closed).
#guard (pubsubPublishGated egTopicCap Notification.empty 0b010).isNone
-- REFUSES: `0b111` exceeds the mask (the `0b010` bit) ⇒ `none`.
#guard (pubsubPublishGated egTopicCap Notification.empty 0b111).isNone
-- ATTENUATED SUBSCRIBER receives a SUBSET: attenuate `0b101 → 0b001`; the sub-cap REFUSES `0b100`
-- (which the full publisher ADMITTED) but still admits `0b001` — strictly fewer kinds (both polarities).
#guard (subscriberWatchCap egTopicCap .impossible 0b001).isSome
#guard egTopicCap.signalAdmissible 0b100                       -- full publisher admits 0b100
#guard
  match subscriberWatchCap egTopicCap .impossible 0b001 with
  | some sub => !sub.signalAdmissible 0b100 && sub.signalAdmissible 0b001  -- sub: refuses 0b100, admits 0b001
  | none => false
-- REFUSES a widening: attenuate `0b101 → 0b111` (add unheld `0b010`) ⇒ `none`.
#guard (subscriberWatchCap egTopicCap .impossible 0b111).isNone

/-! ### MAILBOX teeth — deliver a held tag (COMMITS), refuse an unheld tag, attenuated ⇒ SUBSET. -/

-- COMMITS: sender-tag `0b001` within the mask ⇒ deliver `some`, OR'ing the tag (owner woken).
#guard (inboxDeliverGated egInboxCap Notification.empty 0b001).isSome
#guard inboxDeliverGated egInboxCap Notification.empty 0b001 == some (Notification.empty.signal 0b001)
-- REFUSES: tag `0b010` not held ⇒ `none` (the sender-set membership, now a held cap; non-holder refused).
#guard (inboxDeliverGated egInboxCap Notification.empty 0b010).isNone
-- ATTENUATED SENDER delivers a SUBSET: `0b101 → 0b100`; sub refuses `0b001`, still admits `0b100`.
#guard
  match egInboxCap.attenuateNotify .impossible 0b100 with
  | some sub => !sub.signalAdmissible 0b001 && sub.signalAdmissible 0b100
  | none => false

/-! ### DYNAMICS teeth — emit a held kind (COMMITS), refuse an unheld kind (ambient emit, now gated). -/

-- COMMITS: event-kind `0b100` within the mask ⇒ emit `some`.
#guard (eventEmitGated egSubjectCap Notification.empty 0b100).isSome
-- REFUSES: kind `0b010` not held ⇒ `none` (the ambient `emit`, now cap-authorized).
#guard (eventEmitGated egSubjectCap Notification.empty 0b010).isNone
-- REFUSES: `0b011` (carries the unheld `0b010` bit) ⇒ `none`.
#guard (eventEmitGated egSubjectCap Notification.empty 0b011).isNone

/-! ### UNIFICATION teeth — the three organ wakes on the SAME inputs are the IDENTICAL result. -/

-- The three gated wakes, on one cap/accumulator/badge, agree exactly (the weld, witnessed): a held badge.
#guard pubsubPublishGated egTopicCap Notification.empty 0b001
        == inboxDeliverGated egTopicCap Notification.empty 0b001
#guard inboxDeliverGated egTopicCap Notification.empty 0b001
        == eventEmitGated egTopicCap Notification.empty 0b001
-- …and on an UNHELD badge: all three REFUSE identically.
#guard pubsubPublishGated egTopicCap Notification.empty 0b010
        == eventEmitGated egTopicCap Notification.empty 0b010
#guard (eventEmitGated egTopicCap Notification.empty 0b010).isNone

end Witnesses

/-! ## §6 — Axiom hygiene. Every load-bearing weld theorem is checked kernel-clean (only
`propext`/`Classical.choice`/`Quot.sound`). -/

#assert_all_clean [
  pubsubPublish_refuses_unheld_kind,
  pubsubPublish_commits_held_kind,
  pubsubSubscriber_receives_subset,
  inboxDeliver_refuses_unheld_tag,
  inboxDeliver_commits_held_tag,
  inboxSender_delivers_subset,
  eventEmit_refuses_unheld_kind,
  eventEmit_commits_held_kind,
  organ_wakes_are_one_notify_authority,
  organ_wake_attenuation_no_amplify,
  pubsub_publish_no_amplify,
  inbox_deliver_no_amplify,
  event_emit_no_amplify,
  organ_wakes_are_definitionally_one
]

end Dregg2.Firmament.NotifyOrgans
