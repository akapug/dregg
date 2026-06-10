/-
# Dregg2.Circuit.Spec.queuefifocore — INDEPENDENT full-state spec + executor⟺spec for the
`queue-fifo-core` effect family (the `FullActionA.queueAllocateA` / `.queueResizeA` /
`.queueEnqueueA` / `.queueDequeueA` variants).

This is a LEAF module (imported by nothing; gated standalone). It is the `Transfer.lean` reference
pattern (`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`) re-derived INDEPENDENTLY for
the REAL ring-buffer FIFO queue effects the unified action executor `execFullA` dispatches:

    execFullA s (.queueAllocateA id actor cell cap) = queueAllocateChainA s id actor cell cap   -- :3569
    execFullA s (.queueResizeA id newCap actor cell) = queueResizeChainA s id newCap actor cell -- :3572
    execFullA s (.queueEnqueueA id m actor cell) = queueEnqueueChainA s id m actor cell        -- :3570
    execFullA s (.queueDequeueA id actor cell) = queueDequeueChainA s id actor cell             -- :3571

## Scope of this leaf (truthful)

Two of the four variants — **`queueAllocateA`** and **`queueResizeA`** — are balance-NEUTRAL: they
touch ONLY the `queues` side-table and the chained `log`. The other 16 kernel components are the
FRAME. These two are given the FULL apex treatment below (independent spec, executor⟺spec BOTH
directions, declarative post-state-helper validation, non-vacuity).

The remaining two — **`queueEnqueueA`** and **`queueDequeueA`** — are (F1b) balance-NEUTRAL again:
the Wave-8 refundable anti-spam deposit-park/refund is GONE with the kernel escrow holding-store
(anti-spam deposits re-land as a FACTORY concern in the F2 queue migration). Each touches ONLY the
`queues` side-table + the chained `log`; the other kernel components are the FRAME. They get the
SAME apex treatment — the executor⟺spec is proved BOTH directions — so the family is complete.

## What is proved (the apex reference truth, BOTH directions)

For EACH of the four variants `<V>`:
  * `Queue<V>Spec st … st'` — the INDEPENDENT declarative full-state post-condition: the
    admissibility guard, the EXACT post-state on the touched component(s), the chained `log` advanced
    by exactly the receipt row, AND the FRAME — every OTHER RecordKernelState component LITERALLY
    unchanged. No frame clause mentions the executor's helpers. All 17 kernel components + log are
    enumerated; missing ANY field reintroduces a ghost.
  * a declarative validation lemma for the post-state helper (the freshly-inserted/replaced queue
    record / the FIFO append / the FIFO pop), so the spec's `queues` clause genuinely
    encodes the effect rather than blind-trusting the executor's body.
  * `execFullA_queue<V>A_iff_spec` — execFullA ⟺ spec (BOTH directions). The `→` VALIDATES the
    executor against the independent spec — all 17 kernel fields + log are checked, so a silently
    mutated field would make the proof FAIL; the `←` reconstructs the committed state from the spec.
  * Non-vacuity: each forged input fails a guard leg ⇒ the executor returns `none` ⇒ no spec
    post-state exists.

## FRAME-GAP findings (surfaced by the proofs, NOT silently fixed)

  * **owner = actor (NOT cell).** `queueAllocateChainA s id actor cell cap` allocates with
    `owner := actor` (it calls `queueAllocateK s.kernel id actor capacity`, passing `actor` as the
    owner). The task brief said `owner = cell`; the EXECUTOR uses `actor`. The spec faithfully pins
    `owner := actor` (the brief is wrong, not the code). This is an interface fact worth a human
    glance, not a frame bug.
  * **NO `cap > 0` guard on allocate.** The brief listed `cap > 0` as an admissibility leg;
    `queueAllocateK` accepts ANY `capacity : Nat` (including `0` — a zero-capacity queue that can
    never enqueue). The executor's allocate guard is ONLY `stateAuthB ∧ freshness`. The spec pins
    exactly that. (Not a frame mutation; a missing guard the brief assumed.)
  * **`acceptsEffects` asymmetry.** allocate's guard is `stateAuthB` ALONE; resize/enqueue/dequeue
    additionally require `acceptsEffects s.kernel cell = true` (the lifecycle-liveness gate). Faithful
    to the executor; pinned per-variant.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Circuit.Spec.QueueFifoCore

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)

/-! ## §1 — `queueAllocateA` — the freshly-allocated FIFO queue (balance-NEUTRAL, one component).

`execFullA s (.queueAllocateA id actor cell cap) = queueAllocateChainA s id actor cell cap`
(`TurnExecutorFull:3569`).

    queueAllocateChainA s id actor cell cap                                       -- :2026
      = if stateAuthB s.kernel.caps actor cell = true then
          match queueAllocateK s.kernel id actor cap with
          | some k' => some { kernel := k', log := {actor, src:=cell, dst:=cell, amt:=0} :: s.log }
          | none    => none
        else none

    queueAllocateK k id owner capacity                                            -- RecordKernel:2103
      = match findQueue k.queues id with
        | some _ => none
        | none   => some { k with queues := {id, owner, capacity, buffer := []} :: k.queues }

So the admissibility guard is: `stateAuthB caps actor cell = true ∧ findQueue queues id = none`
(authority over the representing cell ∧ id FRESHNESS). On commit the ONLY kernel component touched is
`queues` (a fresh record prepended, `owner := actor`); the `log` advances by the allocate receipt
`{actor, src:=cell, dst:=cell, amt:=0}`; the other 16 kernel fields are the FRAME. -/

/-- The allocate admissibility guard, as a `Prop` — exactly the two legs `queueAllocateChainA`
checks (authority over `cell`, then `queueAllocateK`'s id-freshness). -/
def allocateGuard (k : RecordKernelState) (id : Nat) (actor cell : CellId) : Prop :=
  stateAuthB k.caps actor cell = true ∧ findQueue k.queues id = none

/-- The fresh queue record an allocate inserts (declarative form — `owner := actor`, the EXECUTOR's
choice; see the FRAME-GAP note in the header). Stated HERE so the spec's `queues` clause does not
reference the executor's body. -/
def freshQueue (id : Nat) (actor : CellId) (capacity : Nat) : QueueRecord :=
  { id := id, owner := actor, capacity := capacity, buffer := [] }

/-- The allocate receipt row (the chained `log` advance). -/
def allocateReceipt (actor cell : CellId) : Turn :=
  { actor := actor, src := cell, dst := cell, amt := 0 }

/-- **`queueAllocateK_correct`** — the allocate post-state helper validated DECLARATIVELY: on a fresh
id, `queueAllocateK` prepends EXACTLY `freshQueue` onto `queues` and leaves every other kernel
component unchanged. So the spec's `queues` clause genuinely encodes prepend ∧ kernel-frame. -/
theorem queueAllocateK_correct (k : RecordKernelState) (id : Nat) (owner : CellId) (capacity : Nat)
    (hfresh : findQueue k.queues id = none) :
    queueAllocateK k id owner capacity
      = some { k with queues := { id := id, owner := owner, capacity := capacity, buffer := [] } :: k.queues } := by
  unfold queueAllocateK
  rw [hfresh]

/-- **The full-state declarative spec of a committed `queueAllocateA`** — the INDEPENDENT reference
semantics. The guard holds (`allocateGuard`); the post-`queues` table is `freshQueue :: st.queues`;
the chained `log` is `allocateReceipt actor cell :: st.log`; and every one of the 16 other
RecordKernelState components is LITERALLY unchanged (the FRAME). No frame clause references the
executor. -/
def QueueAllocateSpec (st : RecChainedState) (id : Nat) (actor cell : CellId) (cap : Nat)
    (st' : RecChainedState) : Prop :=
  allocateGuard st.kernel id actor cell
  ∧ st'.kernel.queues = freshQueue id actor cap :: st.kernel.queues
  ∧ st'.log = allocateReceipt actor cell :: st.log
  -- THE FRAME: every non-`queues` RecordKernelState field, literally unchanged (16).
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.bal = st.kernel.bal
  ∧ st'.kernel.swiss = st.kernel.swiss
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.sealedBoxes = st.kernel.sealedBoxes
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  ∧ st'.kernel.delegationEpochAt = st.kernel.delegationEpochAt

/-- **`queueAllocateChainA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions)** on the chained
allocate step. `queueAllocateChainA` commits a fresh queue into `st'` IFF `st'` is EXACTLY the spec'd
full post-state. The `→` VALIDATES `queueAllocateChainA` against the independent spec — all 17 kernel
components (`queues` + the 16 frame fields) AND the log are checked, so a silently mutated field would
make the proof FAIL; the `←` reconstructs the committed state from the spec. -/
theorem queueAllocateChainA_iff_spec (st : RecChainedState) (id : Nat) (actor cell : CellId) (cap : Nat)
    (st' : RecChainedState) :
    queueAllocateChainA st id actor cell cap = some st'
      ↔ QueueAllocateSpec st id actor cell cap st' := by
  unfold queueAllocateChainA QueueAllocateSpec allocateGuard queueAllocateK
  by_cases hauth : stateAuthB st.kernel.caps actor cell = true
  · rw [if_pos hauth]
    cases hfresh : findQueue st.kernel.queues id with
    | some q =>
        -- duplicate id ⇒ `queueAllocateK = none` ⇒ chain = none; spec's freshness leg also fails.
        simp only
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨⟨_, hf⟩, _⟩; exact absurd hf (by simp)
    | none =>
        simp only [freshQueue, allocateReceipt]
        constructor
        · intro h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨⟨hauth, trivial⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                 rfl, rfl, rfl, rfl, rfl, rfl⟩
        · rintro ⟨_, hq, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
          obtain ⟨k', l'⟩ := st'
          obtain ⟨acc, cell0, caps, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb, dge, dgea⟩ := k'
          simp only at hq hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
          subst hq hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
          rfl
  · rw [if_neg hauth]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hg, _⟩, _⟩; exact absurd hg hauth

/-- **`execFullA_queueAllocateA_iff_spec` — the UNIFIED-ACTION executor corner.** `execFullA`
dispatches `.queueAllocateA …` to `queueAllocateChainA s …`, so committing the unified action into
`st'` is EXACTLY the full-state spec. -/
theorem execFullA_queueAllocateA_iff_spec (st : RecChainedState) (id : Nat) (actor cell : CellId)
    (cap : Nat) (st' : RecChainedState) :
    execFullA st (.queueAllocateA id actor cell cap) = some st'
      ↔ QueueAllocateSpec st id actor cell cap st' := by
  show queueAllocateChainA st id actor cell cap = some st' ↔ QueueAllocateSpec st id actor cell cap st'
  exact queueAllocateChainA_iff_spec st id actor cell cap st'

/-! ### allocate post-state corollaries (read off the spec). -/

/-- **`allocate_inserts_fresh`** — a committed allocate prepends EXACTLY the fresh queue record (with
`owner := actor`, empty buffer, the given capacity) onto the side-table. -/
theorem allocate_inserts_fresh (st : RecChainedState) (id : Nat) (actor cell : CellId) (cap : Nat)
    (st' : RecChainedState)
    (h : execFullA st (.queueAllocateA id actor cell cap) = some st') :
    st'.kernel.queues = freshQueue id actor cap :: st.kernel.queues :=
  ((execFullA_queueAllocateA_iff_spec st id actor cell cap st').mp h).2.1

/-- **`allocate_balNeutral_ledger`** — a committed allocate leaves the entire per-asset `bal` ledger
unchanged (queues hold MESSAGES, never balance). -/
theorem allocate_balNeutral_ledger (st : RecChainedState) (id : Nat) (actor cell : CellId) (cap : Nat)
    (st' : RecChainedState)
    (h : execFullA st (.queueAllocateA id actor cell cap) = some st') :
    st'.kernel.bal = st.kernel.bal :=
  ((execFullA_queueAllocateA_iff_spec st id actor cell cap st').mp h).2.2.2.2.2.2.2.2.2.1

/-! ### allocate non-vacuity (each guard leg, fail-closed). -/

/-- **`allocate_rejects_unauthorized` — PROVED.** An actor lacking authority over `cell` cannot
allocate ⇒ no `st'` satisfies the spec. -/
theorem allocate_rejects_unauthorized (st : RecChainedState) (id : Nat) (actor cell : CellId) (cap : Nat)
    (hbad : stateAuthB st.kernel.caps actor cell = false) :
    execFullA st (.queueAllocateA id actor cell cap) = none := by
  show queueAllocateChainA st id actor cell cap = none
  unfold queueAllocateChainA
  rw [if_neg (by rw [hbad]; simp)]

/-- **`allocate_rejects_id_reuse` — PROVED.** An allocate whose `id` is ALREADY a live queue does NOT
commit (the FRESHNESS leg fails) — queue ids cannot collide on the side-table. -/
theorem allocate_rejects_id_reuse (st : RecChainedState) (id : Nat) (actor cell : CellId) (cap : Nat)
    (q : QueueRecord) (hbad : findQueue st.kernel.queues id = some q) :
    execFullA st (.queueAllocateA id actor cell cap) = none := by
  show queueAllocateChainA st id actor cell cap = none
  unfold queueAllocateChainA queueAllocateK
  by_cases hauth : stateAuthB st.kernel.caps actor cell = true
  · rw [if_pos hauth, hbad]
  · rw [if_neg hauth]

/-! ## §2 — `queueResizeA` — re-cap an existing FIFO queue (balance-NEUTRAL, one component).

`execFullA s (.queueResizeA id newCap actor cell) = queueResizeChainA s id newCap actor cell`
(`TurnExecutorFull:3572`).

    queueResizeChainA s id newCap actor cell                                      -- :2065
      = if stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true then
          match queueResizeK s.kernel id newCap with
          | some k' => some { kernel := k', log := {actor, src:=cell, dst:=cell, amt:=0} :: s.log }
          | none    => none
        else none

    queueResizeK k id newCap                                                      -- RecordKernel:2140
      = match findQueue k.queues id with
        | none   => none
        | some q => if q.buffer.length ≤ newCap then
                      some { k with queues := replaceQueue k.queues id { q with capacity := newCap } }
                    else none

Admissibility: `stateAuthB ∧ acceptsEffects cell ∧ ∃ q, findQueue queues id = some q ∧
q.buffer.length ≤ newCap` (authority ∧ lifecycle-liveness ∧ queue EXISTS ∧ can't shrink below
current occupancy). On commit the ONLY kernel component touched is `queues` (the record re-capped via
`replaceQueue`, buffer untouched); the `log` advances by the resize receipt; the other 16 kernel
fields are the FRAME. -/

/-- The resize admissibility guard, as a `Prop` — authority, lifecycle-liveness, queue existence, and
the no-shrink-below-occupancy bound `queueResizeK` checks. -/
def resizeGuard (k : RecordKernelState) (id : Nat) (newCap : Nat) (actor cell : CellId) : Prop :=
  stateAuthB k.caps actor cell = true ∧ acceptsEffects k cell = true
    ∧ ∃ q, findQueue k.queues id = some q ∧ q.buffer.length ≤ newCap

/-- The resize receipt row (the chained `log` advance — a clock row, `amt := 0`). -/
def resizeReceipt (actor cell : CellId) : Turn :=
  { actor := actor, src := cell, dst := cell, amt := 0 }

/-- **`queueResizeK_correct`** — the resize post-state helper validated DECLARATIVELY: on an existing
queue `q` whose occupancy fits `newCap`, `queueResizeK` replaces `q` by `{q with capacity := newCap}`
(buffer UNCHANGED) in `queues` and leaves every other kernel component unchanged. So the spec's
`queues` clause genuinely encodes a capacity-only re-cap. -/
theorem queueResizeK_correct (k : RecordKernelState) (id newCap : Nat) (q : QueueRecord)
    (hq : findQueue k.queues id = some q) (hcap : q.buffer.length ≤ newCap) :
    queueResizeK k id newCap
      = some { k with queues := replaceQueue k.queues id { q with capacity := newCap } } := by
  unfold queueResizeK
  simp only [hq, if_pos hcap]

/-- **The full-state declarative spec of a committed `queueResizeA`** — the INDEPENDENT reference
semantics. The guard holds (`resizeGuard`); the post-`queues` table is the witnessed queue re-capped
in place via `replaceQueue`; the chained `log` is `resizeReceipt actor cell :: st.log`; and every one
of the 16 other RecordKernelState components is LITERALLY unchanged (the FRAME). -/
def QueueResizeSpec (st : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (st' : RecChainedState) : Prop :=
  resizeGuard st.kernel id newCap actor cell
  ∧ (∀ q, findQueue st.kernel.queues id = some q →
        st'.kernel.queues = replaceQueue st.kernel.queues id { q with capacity := newCap })
  ∧ st'.log = resizeReceipt actor cell :: st.log
  -- THE FRAME: every non-`queues` RecordKernelState field, literally unchanged (16).
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.bal = st.kernel.bal
  ∧ st'.kernel.swiss = st.kernel.swiss
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.sealedBoxes = st.kernel.sealedBoxes
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  ∧ st'.kernel.delegationEpochAt = st.kernel.delegationEpochAt

/-- **`queueResizeChainA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions)** on the chained
resize step. The `→` VALIDATES `queueResizeChainA` against the independent spec — all 17 kernel
components AND the log are checked; the `←` reconstructs the committed state from the spec. -/
theorem queueResizeChainA_iff_spec (st : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (st' : RecChainedState) :
    queueResizeChainA st id newCap actor cell = some st'
      ↔ QueueResizeSpec st id newCap actor cell st' := by
  unfold queueResizeChainA QueueResizeSpec resizeGuard queueResizeK
  by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
  · rw [if_pos hg]
    obtain ⟨hauth, hacc⟩ := hg
    cases hf : findQueue st.kernel.queues id with
    | none =>
        simp only
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨⟨_, _, q, hq, _⟩, _⟩; exact absurd hq (by simp)
    | some q =>
        by_cases hcap : q.buffer.length ≤ newCap
        · simp only [if_pos hcap, resizeReceipt]
          constructor
          · intro h
            simp only [Option.some.injEq] at h
            subst h
            refine ⟨⟨hauth, hacc, q, rfl, hcap⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            intro q' hq'; simp only [Option.some.injEq] at hq'; subst hq'; rfl
          · rintro ⟨_, hq, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
            have hqeq := hq q rfl
            obtain ⟨k', l'⟩ := st'
            obtain ⟨acc, cell0, caps, nul, rev, com, bal, qs, sw, sc, fac, lc, dc, dg, dgs, sb, dge, dgea⟩ := k'
            simp only at hqeq hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
            subst hqeq hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
            rfl
        · simp only [if_neg hcap]
          constructor
          · intro h; exact absurd h (by simp)
          · rintro ⟨⟨_, _, q', hq', hcap'⟩, _⟩
            simp only [Option.some.injEq] at hq'; subst hq'; exact absurd hcap' hcap
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hauth, hacc, _⟩, _⟩; exact absurd ⟨hauth, hacc⟩ hg

/-- **`execFullA_queueResizeA_iff_spec` — the UNIFIED-ACTION executor corner.** -/
theorem execFullA_queueResizeA_iff_spec (st : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (st' : RecChainedState) :
    execFullA st (.queueResizeA id newCap actor cell) = some st'
      ↔ QueueResizeSpec st id newCap actor cell st' := by
  show queueResizeChainA st id newCap actor cell = some st' ↔ QueueResizeSpec st id newCap actor cell st'
  exact queueResizeChainA_iff_spec st id newCap actor cell st'

/-! ### resize non-vacuity (each guard leg, fail-closed). -/

/-- **`resize_rejects_unauthorized` — PROVED.** -/
theorem resize_rejects_unauthorized (st : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (hbad : stateAuthB st.kernel.caps actor cell = false) :
    execFullA st (.queueResizeA id newCap actor cell) = none := by
  show queueResizeChainA st id newCap actor cell = none
  unfold queueResizeChainA
  rw [if_neg (by rw [hbad]; rintro ⟨h, _⟩; exact absurd h (by simp))]

/-- **`resize_rejects_dead_cell` — PROVED.** A resize on a non-Live cell (`acceptsEffects = false`)
does NOT commit (the lifecycle-liveness leg fails). -/
theorem resize_rejects_dead_cell (st : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (hbad : acceptsEffects st.kernel cell = false) :
    execFullA st (.queueResizeA id newCap actor cell) = none := by
  show queueResizeChainA st id newCap actor cell = none
  unfold queueResizeChainA
  rw [if_neg (by rw [hbad]; rintro ⟨_, h⟩; exact absurd h (by simp))]

/-- **`resize_rejects_absent` — PROVED.** A resize of a non-existent queue does NOT commit. -/
theorem resize_rejects_absent (st : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (hbad : findQueue st.kernel.queues id = none) :
    execFullA st (.queueResizeA id newCap actor cell) = none := by
  show queueResizeChainA st id newCap actor cell = none
  unfold queueResizeChainA queueResizeK
  simp only [hbad]
  by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
  · rw [if_pos hg]
  · rw [if_neg hg]

/-- **`resize_rejects_shrink_below_occupancy` — PROVED.** A resize whose `newCap` is below the
queue's current occupancy does NOT commit (the no-shrink bound fails) — pending messages cannot be
silently dropped. -/
theorem resize_rejects_shrink_below_occupancy (st : RecChainedState) (id newCap : Nat)
    (actor cell : CellId) (q : QueueRecord)
    (hq : findQueue st.kernel.queues id = some q) (hbad : ¬ q.buffer.length ≤ newCap) :
    execFullA st (.queueResizeA id newCap actor cell) = none := by
  show queueResizeChainA st id newCap actor cell = none
  unfold queueResizeChainA queueResizeK
  simp only [hq, if_neg hbad]
  by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
  · rw [if_pos hg]
  · rw [if_neg hg]

/-! ## §3 — `queueEnqueueA` — FIFO append (balance-NEUTRAL, one component).

F1b: the Wave-8 refundable anti-spam deposit-park is GONE with the kernel escrow holding-store it
parked into (anti-spam deposits are a FACTORY concern in the F2 queue migration). The enqueue is the
bare FIFO append again:

    queueEnqueueChainA s id m actor cell                                          -- :2072
      = if stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true then
          match queueEnqueueK s.kernel id m with
          | some k' => some { kernel := k', log := {actor, src:=cell, dst:=cell, amt:=0} :: s.log }
          | none    => none
        else none

Admissibility: `stateAuthB ∧ acceptsEffects cell ∧ ∃ q, findQueue queues id = some q ∧
q.buffer.length < q.capacity` (authority ∧ lifecycle-liveness ∧ queue EXISTS ∧ not FULL). On commit
the ONLY kernel component touched is `queues` (the record's buffer tail-appended via `replaceQueue`);
the `log` advances by the enqueue receipt; the other kernel fields are the FRAME. -/

/-- The enqueue admissibility guard, as a `Prop` — authority, lifecycle-liveness, queue existence,
and the capacity bound `queueEnqueueK` checks. -/
def enqueueGuard (k : RecordKernelState) (id m : Nat) (actor cell : CellId) : Prop :=
  stateAuthB k.caps actor cell = true ∧ acceptsEffects k cell = true
    ∧ ∃ q, findQueue k.queues id = some q ∧ q.buffer.length < q.capacity

/-- The enqueue receipt row (the chained `log` advance — a clock row, `amt := 0`). -/
def enqueueReceipt (actor cell : CellId) : Turn :=
  { actor := actor, src := cell, dst := cell, amt := 0 }

/-- **`queueEnqueueK_correct`** — the enqueue post-state helper validated DECLARATIVELY: on an
existing queue `q` with free capacity, `queueEnqueueK` replaces `q` by the tail-appended record
(every other kernel component unchanged). So the spec's `queues` clause genuinely encodes a
buffer-only FIFO append. -/
theorem queueEnqueueK_correct (k : RecordKernelState) (id m : Nat) (q : QueueRecord)
    (hq : findQueue k.queues id = some q) (hcap : q.buffer.length < q.capacity) :
    queueEnqueueK k id m
      = some { k with queues := replaceQueue k.queues id { q with buffer := qbufEnqueue q.buffer m } } := by
  unfold queueEnqueueK
  simp only [hq, if_pos hcap]

/-- **The full-state declarative spec of a committed `queueEnqueueA`** — the INDEPENDENT reference
semantics. The guard holds (`enqueueGuard`); the post-`queues` table is the witnessed queue with `m`
appended to its buffer tail; the chained `log` is `enqueueReceipt actor cell :: st.log`; and every
other RecordKernelState component is LITERALLY unchanged (the FRAME). -/
def QueueEnqueueSpec (st : RecChainedState) (id m : Nat) (actor cell : CellId)
    (st' : RecChainedState) : Prop :=
  enqueueGuard st.kernel id m actor cell
  ∧ (∀ q, findQueue st.kernel.queues id = some q →
        st'.kernel.queues = replaceQueue st.kernel.queues id { q with buffer := qbufEnqueue q.buffer m })
  ∧ st'.log = enqueueReceipt actor cell :: st.log
  -- THE FRAME: every non-`queues` RecordKernelState field, literally unchanged.
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.bal = st.kernel.bal
  ∧ st'.kernel.swiss = st.kernel.swiss
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.sealedBoxes = st.kernel.sealedBoxes
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  ∧ st'.kernel.delegationEpochAt = st.kernel.delegationEpochAt

/-- **`queueEnqueueChainA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions)** on the chained
enqueue step. The `→` VALIDATES `queueEnqueueChainA` against the independent spec — all kernel
components AND the log are checked; the `←` reconstructs the committed state from the spec. -/
theorem queueEnqueueChainA_iff_spec (st : RecChainedState) (id m : Nat) (actor cell : CellId)
    (st' : RecChainedState) :
    queueEnqueueChainA st id m actor cell = some st'
      ↔ QueueEnqueueSpec st id m actor cell st' := by
  unfold queueEnqueueChainA QueueEnqueueSpec enqueueGuard queueEnqueueK
  by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
  · rw [if_pos hg]
    obtain ⟨hauth, hacc⟩ := hg
    cases hf : findQueue st.kernel.queues id with
    | none =>
        simp only
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨⟨_, _, q, hq, _⟩, _⟩; exact absurd hq (by simp)
    | some q =>
        by_cases hcap : q.buffer.length < q.capacity
        · simp only [if_pos hcap, enqueueReceipt]
          constructor
          · intro h
            simp only [Option.some.injEq] at h
            subst h
            refine ⟨⟨hauth, hacc, q, rfl, hcap⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            intro q' hq'; simp only [Option.some.injEq] at hq'; subst hq'; rfl
          · rintro ⟨_, hq, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
            have hqeq := hq q rfl
            obtain ⟨k', l'⟩ := st'
            obtain ⟨acc, cell0, caps, nul, rev, com, bal, qs, sw, sc, fac, lc, dc, dg, dgs, sb, dge, dgea⟩ := k'
            simp only at hqeq hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
            subst hqeq hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
            rfl
        · simp only [if_neg hcap]
          constructor
          · intro h; exact absurd h (by simp)
          · rintro ⟨⟨_, _, q', hq', hcap'⟩, _⟩
            simp only [Option.some.injEq] at hq'; subst hq'; exact absurd hcap' hcap
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hauth, hacc, _⟩, _⟩; exact absurd ⟨hauth, hacc⟩ hg

/-- **`execFullA_queueEnqueueA_iff_spec` — the UNIFIED-ACTION executor corner.** -/
theorem execFullA_queueEnqueueA_iff_spec (st : RecChainedState) (id m : Nat) (actor cell : CellId)
    (st' : RecChainedState) :
    execFullA st (.queueEnqueueA id m actor cell) = some st'
      ↔ QueueEnqueueSpec st id m actor cell st' := by
  show queueEnqueueChainA st id m actor cell = some st' ↔ QueueEnqueueSpec st id m actor cell st'
  exact queueEnqueueChainA_iff_spec st id m actor cell st'

/-! ### enqueue non-vacuity. -/

/-- **`enqueue_rejects_unauthorized` — PROVED.** -/
theorem enqueue_rejects_unauthorized (st : RecChainedState) (id m : Nat) (actor cell : CellId)
    (hbad : stateAuthB st.kernel.caps actor cell = false) :
    execFullA st (.queueEnqueueA id m actor cell) = none := by
  show queueEnqueueChainA st id m actor cell = none
  unfold queueEnqueueChainA
  rw [if_neg (by rw [hbad]; rintro ⟨h, _⟩; exact absurd h (by simp))]

/-- **`enqueue_rejects_dead_cell` — PROVED.** An enqueue through a non-Live cell does NOT commit. -/
theorem enqueue_rejects_dead_cell (st : RecChainedState) (id m : Nat) (actor cell : CellId)
    (hbad : acceptsEffects st.kernel cell = false) :
    execFullA st (.queueEnqueueA id m actor cell) = none := by
  show queueEnqueueChainA st id m actor cell = none
  unfold queueEnqueueChainA
  rw [if_neg (by rw [hbad]; rintro ⟨_, h⟩; exact absurd h (by simp))]

/-- **`enqueue_rejects_full` — PROVED.** An enqueue into a FULL queue does NOT commit (the ring
capacity bound is real). -/
theorem enqueue_rejects_full (st : RecChainedState) (id m : Nat) (actor cell : CellId)
    (q : QueueRecord) (hq : findQueue st.kernel.queues id = some q)
    (hbad : ¬ q.buffer.length < q.capacity) :
    execFullA st (.queueEnqueueA id m actor cell) = none := by
  show queueEnqueueChainA st id m actor cell = none
  unfold queueEnqueueChainA queueEnqueueK
  simp only [hq, if_neg hbad]
  by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
  · rw [if_pos hg]
  · rw [if_neg hg]

/-! ## §4 — `queueDequeueA` — FIFO pop-front (balance-NEUTRAL, one component).

F1b: the deposit refund is GONE with the deposit park — the dequeue is the bare owner-gated FIFO
REMOVE-FROM-FRONT again:

    queueDequeueChainA s id actor cell                                            -- :2085
      = if stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true then
          match queueDequeueK s.kernel id actor with
          | some (k', _) => some { kernel := k', log := {actor, src:=cell, dst:=cell, amt:=0} :: s.log }
          | none         => none
        else none

Admissibility: `stateAuthB ∧ acceptsEffects cell ∧ ∃ q m rest, findQueue queues id = some q ∧
actor = q.owner ∧ qbufDequeue q.buffer = some (m, rest)` (authority ∧ liveness ∧ queue EXISTS ∧
OWNER-only ∧ non-EMPTY). On commit the ONLY kernel component touched is `queues` (the record's
buffer popped via `replaceQueue`); the `log` advances by the dequeue receipt. -/

/-- The dequeue admissibility guard, as a `Prop` — authority, lifecycle-liveness, queue existence,
the owner-only gate, and non-emptiness (witnessed by the popped head + rest). -/
def dequeueGuard (k : RecordKernelState) (id : Nat) (actor cell : CellId) : Prop :=
  stateAuthB k.caps actor cell = true ∧ acceptsEffects k cell = true
    ∧ ∃ q m rest, findQueue k.queues id = some q ∧ actor = q.owner
        ∧ qbufDequeue q.buffer = some (m, rest)

/-- The dequeue receipt row (the chained `log` advance — a clock row, `amt := 0`). -/
def dequeueReceipt (actor cell : CellId) : Turn :=
  { actor := actor, src := cell, dst := cell, amt := 0 }

/-- **`queueDequeueK_correct`** — the dequeue post-state helper validated DECLARATIVELY: on an
existing queue `q` owned by `actor` with head `m` and remainder `rest`, `queueDequeueK` replaces `q`
by the popped record and surfaces `m` (every other kernel component unchanged). -/
theorem queueDequeueK_correct (k : RecordKernelState) (id : Nat) (actor : CellId) (q : QueueRecord)
    (m : Nat) (rest : List Nat) (hq : findQueue k.queues id = some q) (ho : actor = q.owner)
    (hd : qbufDequeue q.buffer = some (m, rest)) :
    queueDequeueK k id actor
      = some ({ k with queues := replaceQueue k.queues id { q with buffer := rest } }, m) := by
  unfold queueDequeueK
  simp only [hq, if_pos ho, hd]

/-- **The full-state declarative spec of a committed `queueDequeueA`** — the INDEPENDENT reference
semantics. The guard holds (`dequeueGuard`); the post-`queues` table is the witnessed queue with its
FIFO head popped; the chained `log` is `dequeueReceipt actor cell :: st.log`; and every other
RecordKernelState component is LITERALLY unchanged (the FRAME). -/
def QueueDequeueSpec (st : RecChainedState) (id : Nat) (actor cell : CellId)
    (st' : RecChainedState) : Prop :=
  dequeueGuard st.kernel id actor cell
  ∧ (∀ q m rest, findQueue st.kernel.queues id = some q → qbufDequeue q.buffer = some (m, rest) →
        st'.kernel.queues = replaceQueue st.kernel.queues id { q with buffer := rest })
  ∧ st'.log = dequeueReceipt actor cell :: st.log
  -- THE FRAME: every non-`queues` RecordKernelState field, literally unchanged.
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.bal = st.kernel.bal
  ∧ st'.kernel.swiss = st.kernel.swiss
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.sealedBoxes = st.kernel.sealedBoxes
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  ∧ st'.kernel.delegationEpochAt = st.kernel.delegationEpochAt

/-- **`queueDequeueChainA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions)** on the chained
dequeue step. The `→` VALIDATES `queueDequeueChainA` against the independent spec; the `←`
reconstructs the committed state from the spec. -/
theorem queueDequeueChainA_iff_spec (st : RecChainedState) (id : Nat) (actor cell : CellId)
    (st' : RecChainedState) :
    queueDequeueChainA st id actor cell = some st'
      ↔ QueueDequeueSpec st id actor cell st' := by
  unfold queueDequeueChainA QueueDequeueSpec dequeueGuard queueDequeueK
  by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
  · rw [if_pos hg]
    obtain ⟨hauth, hacc⟩ := hg
    cases hf : findQueue st.kernel.queues id with
    | none =>
        simp only
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨⟨_, _, q, m, rest, hq, _⟩, _⟩; exact absurd hq (by simp)
    | some q =>
        by_cases ho : actor = q.owner
        · simp only [if_pos ho]
          cases hd : qbufDequeue q.buffer with
          | none =>
              constructor
              · intro h; exact absurd h (by simp)
              · rintro ⟨⟨_, _, q', m', rest', hq', _, hd'⟩, _⟩
                simp only [Option.some.injEq] at hq'; subst hq'
                rw [hd] at hd'; exact absurd hd' (by simp)
          | some hr =>
              obtain ⟨m0, rest0⟩ := hr
              simp only [dequeueReceipt]
              constructor
              · intro h
                simp only [Option.some.injEq] at h
                subst h
                refine ⟨⟨hauth, hacc, q, m0, rest0, rfl, ho, hd⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
                        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                intro q' m' rest' hq' hd'
                simp only [Option.some.injEq] at hq'; subst hq'
                rw [hd] at hd'; simp only [Option.some.injEq, Prod.mk.injEq] at hd'
                rw [hd'.2]
              · rintro ⟨_, hq, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
                have hqeq := hq q m0 rest0 rfl hd
                obtain ⟨k', l'⟩ := st'
                obtain ⟨acc, cell0, caps, nul, rev, com, bal, qs, sw, sc, fac, lc, dc, dg, dgs, sb, dge, dgea⟩ := k'
                simp only at hqeq hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
                subst hqeq hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
                rfl
        · simp only [if_neg ho]
          constructor
          · intro h; exact absurd h (by simp)
          · rintro ⟨⟨_, _, q', m', rest', hq', ho', _⟩, _⟩
            simp only [Option.some.injEq] at hq'; subst hq'; exact absurd ho' ho
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hauth, hacc, _⟩, _⟩; exact absurd ⟨hauth, hacc⟩ hg

/-- **`execFullA_queueDequeueA_iff_spec` — the UNIFIED-ACTION executor corner.** -/
theorem execFullA_queueDequeueA_iff_spec (st : RecChainedState) (id : Nat) (actor cell : CellId)
    (st' : RecChainedState) :
    execFullA st (.queueDequeueA id actor cell) = some st'
      ↔ QueueDequeueSpec st id actor cell st' := by
  show queueDequeueChainA st id actor cell = some st' ↔ QueueDequeueSpec st id actor cell st'
  exact queueDequeueChainA_iff_spec st id actor cell st'

/-! ### dequeue non-vacuity. -/

/-- **`dequeue_rejects_unauthorized` — PROVED.** -/
theorem dequeue_rejects_unauthorized (st : RecChainedState) (id : Nat) (actor cell : CellId)
    (hbad : stateAuthB st.kernel.caps actor cell = false) :
    execFullA st (.queueDequeueA id actor cell) = none := by
  show queueDequeueChainA st id actor cell = none
  unfold queueDequeueChainA
  rw [if_neg (by rw [hbad]; rintro ⟨h, _⟩; exact absurd h (by simp))]

/-- **`dequeue_rejects_dead_cell` — PROVED.** A dequeue through a non-Live cell does NOT commit. -/
theorem dequeue_rejects_dead_cell (st : RecChainedState) (id : Nat) (actor cell : CellId)
    (hbad : acceptsEffects st.kernel cell = false) :
    execFullA st (.queueDequeueA id actor cell) = none := by
  show queueDequeueChainA st id actor cell = none
  unfold queueDequeueChainA
  rw [if_neg (by rw [hbad]; rintro ⟨_, h⟩; exact absurd h (by simp))]

/-- **`dequeue_rejects_non_owner` — PROVED.** A dequeuer that is NOT the queue owner does NOT
commit (the owner-only gate, `apply.rs:3433`). -/
theorem dequeue_rejects_non_owner (st : RecChainedState) (id : Nat) (actor cell : CellId)
    (q : QueueRecord) (hq : findQueue st.kernel.queues id = some q) (hbad : actor ≠ q.owner) :
    execFullA st (.queueDequeueA id actor cell) = none := by
  show queueDequeueChainA st id actor cell = none
  unfold queueDequeueChainA queueDequeueK
  simp only [hq, if_neg hbad]
  by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
  · rw [if_pos hg]
  · rw [if_neg hg]

/-- **`dequeue_rejects_empty` — PROVED.** A dequeue from an EMPTY queue does NOT commit. -/
theorem dequeue_rejects_empty (st : RecChainedState) (id : Nat) (actor cell : CellId)
    (q : QueueRecord) (hq : findQueue st.kernel.queues id = some q) (hbad : q.buffer = []) :
    execFullA st (.queueDequeueA id actor cell) = none := by
  show queueDequeueChainA st id actor cell = none
  unfold queueDequeueChainA queueDequeueK
  simp only [hq, hbad]
  by_cases ho : actor = q.owner
  · simp only [if_pos ho, qbufDequeue]
    by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
    · rw [if_pos hg]
    · rw [if_neg hg]
  · simp only [if_neg ho]
    by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ acceptsEffects st.kernel cell = true
    · rw [if_pos hg]
    · rw [if_neg hg]

/-! ## §5 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms queueAllocateK_correct
#assert_axioms queueAllocateChainA_iff_spec
#assert_axioms execFullA_queueAllocateA_iff_spec
#assert_axioms allocate_inserts_fresh
#assert_axioms allocate_balNeutral_ledger
#assert_axioms allocate_rejects_unauthorized
#assert_axioms allocate_rejects_id_reuse

#assert_axioms queueResizeK_correct
#assert_axioms queueResizeChainA_iff_spec
#assert_axioms execFullA_queueResizeA_iff_spec
#assert_axioms resize_rejects_unauthorized
#assert_axioms resize_rejects_dead_cell
#assert_axioms resize_rejects_absent
#assert_axioms resize_rejects_shrink_below_occupancy

#assert_axioms queueEnqueueK_correct
#assert_axioms queueEnqueueChainA_iff_spec
#assert_axioms execFullA_queueEnqueueA_iff_spec
#assert_axioms enqueue_rejects_unauthorized
#assert_axioms enqueue_rejects_dead_cell
#assert_axioms enqueue_rejects_full

#assert_axioms queueDequeueK_correct
#assert_axioms queueDequeueChainA_iff_spec
#assert_axioms execFullA_queueDequeueA_iff_spec
#assert_axioms dequeue_rejects_unauthorized
#assert_axioms dequeue_rejects_dead_cell
#assert_axioms dequeue_rejects_non_owner
#assert_axioms dequeue_rejects_empty

end Dregg2.Circuit.Spec.QueueFifoCore
