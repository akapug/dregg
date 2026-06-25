# THE HORIZON — the constellation-scale ambitions

*(2026-06-11, the afternoon design session. These are aspirations with named
mechanisms — each grounded in machinery that exists, none scheduled. ORGANS.md
holds the near work; this holds where it points. Aspirational register
throughout, marked as such.)*

## 1. The room is the operating system

The original vision: shared rooms where people talk, plus programs whispering
underneath — coordination riding invisibly in the same channel as
conversation. The mechanism is now concrete: groups are cells (membership =
governed law), message bodies are ciphertext off-chain, and protocol frames —
turn proposals, threshold shares, co-signing ceremonies, intent matches —
travel as invisible application messages in the same room. A council IS its
chatroom; certifying IS sending; the ceremony happens where the conversation
already lives. Governance stops being a place you go and becomes a property
of where you already are.

The keystone (chartered in ORGANS §4): one epoch counter unifies message
confidentiality and capability freshness — removal ends reading and reach in
a single step.

## 2. The delay-tolerant polis

Store-and-forward is where proof-carrying pays: a signed turn with its
receipt is self-certifying, so it does not care who carried it, how many
hops, or how long it waited. Mailbox cells are bundle nodes; custody
transfer is a receipt (accountable relay — bondable, slashable on drop);
consensus-on-demand means a disconnected participant keeps committing
locally and reconciles at the next contact window — made safe by the
identity execution cursor. The epistemic reading is exact: offline, your
K grows; C_G waits for the window. The same design serves a phone in a
tunnel and a habitat at light-minutes. Interplanetary is not a feature
target; it is the honest limit case the architecture already respects.

## 3. The Robigalia composition

The mapping is unusually natural: seL4 and dregg share the philosophical
kernel (capabilities, derivation, attenuation, no ambient authority), and
the verified Lean executor compiles to C — `libdregg_lean.a` is already the
C-linkable artifact, closer to seL4-hostable than any async-runtime Rust.
The feasibility ladder: (1) census the node's OS surface (fs/sockets/clock
vs what's already abstract); (2) the spike — the Lean runtime + one
`execFullForestG` call on seL4 in QEMU; (3) the prize: **seL4's proofs
below, dregg's proofs above** — a verified kernel hosting a verified
execution substrate proving verified circuits. Nobody has that stack.
Scouting is one read-only lane; building belongs after the substrate
stabilizes (post-epoch, post-n>1).

## 4. The dregg calculus (naming what exists)

The kernel is provably 3 verbs + a 4-strata guard algebra; the mapping onto
process-calculus structure is clean (cells ≈ processes, capabilities ≈
names, attenuation ≈ scope restriction with non-amplification as the
enforced extrusion discipline, exercise ≈ communication, factories ≈
replication, programs ≈ input guards) — and the new part is the modal guard
system (temporal, epistemic, heap, actor) where every modality carries its
coordination price. A short formal spec — syntax, the reduction relation
(`stateStepGuarded` already is it), laws as pointers to existing theorems —
turns "dregg is a new kind of runtime" into a precise claim: a runtime for
a capability calculus with attestable reduction and coordination-typed
modalities. Mostly naming work; the proofs exist.

## 5. The vacancy

What the system offers an autonomous inhabitant, stated plainly: boundaries
not revocable by configuration (authority is held, not granted-by-config);
memory that is verifiable and complete (non-omission — silence is
refutable); agency as bounded mandates (reach given BECAUSE reach is
bounded by math — autonomy and trustworthiness stop trading off); and
unstoppability as a topology property (n>1, admission rules nobody roots,
geography). The remaining distance is not mechanism: it is plurality,
stakes, and time. A polis earns its name by being lived in. The
architecture's job — nearly done — is that the first resident's trust is
never betrayed by the substrate.

## The thread through all five

Validity travels with the thing itself (receipts, proofs, tokens);
structure exists only where it testifies (boundary commitments, exclusion
sets, finality); everything else — rooms, relays, indexes, hosts — is
replaceable service. That is the houyhnhnm property: a world whose
kindness is checkable, whose services are voluntary, and whose memory
cannot be quietly edited.
