/**
 * The **service-economy** SDK surface — buy a service in a few lines, over the
 * verified rail. The hand-written TypeScript twin of the Rust SDK facade
 * (`sdk/src/service_economy.rs`): `pay`, `services.invoke`, and a durable,
 * metered `execution.lease`.
 *
 * Every method here is a THIN, HONEST wrapper that builds the SAME `Action` /
 * `Effect` JSON the node executor verifies — the same bytes the Rust
 * `dregg_payable::resolve_pay` / `resolve_invocation` desugars produce. There
 * is no new kernel effect, no new commitment field, and no faking:
 *
 * - `pay(to, amount, asset)` → the canonical `Payable` `pay` desugar: an
 *   action with `method = pay`, `args = [asset, field_from_u64(amount), to]`,
 *   carrying EXACTLY ONE conserving `Effect::Transfer` (per-asset Σδ=0).
 * - `services.invoke(cell, method, args, { pay })` → an action targeting
 *   `cell`'s method, optionally PREPENDING the canonical pay `Transfer` ahead
 *   of the work effects. The verified DFA route + unknown-method / under-
 *   authority refusal are the node executor's job over the wire (the SDK is a
 *   remote client); the action shape is byte-identical to the Rust desugar.
 * - `execution.lease({ maxSteps, asset, leaseCell })` → a `Lease` whose `run`
 *   advances the durable checkpoint (`step → step+1`, a `SetField` on
 *   {@link LEASE_STEP_SLOT}) alongside the workload on ONE turn, and whose
 *   `fund` is a conserving `Effect::Transfer` into the lease cell.
 *
 * ## What is node-side (the honest boundary)
 *
 * The TS SDK is a wire client: it builds + signs + submits turns. Spawning the
 * cap-gated worker and installing the lease meter program
 * (`FieldLte { step ≤ maxSteps } ∧ Monotonic { step }`, see
 * {@link leaseProgramConstraints}) is the cell-provisioning step the in-process
 * Rust `ExecutionLease::open` does locally; over the wire it is done when the
 * lease cell is provisioned. {@link ServiceEconomy.lease} binds to that lease
 * cell and drives the verified `run` / `fund` turns against it — the executor's
 * meter program is what binds the capacity ceiling into every committed
 * transition, exactly as the standalone `starbridge-execution-lease` app's
 * `advance_checkpoint` relies on.
 */

import type { AgentRuntime } from "./client";
import type { Receipt } from "./receipt";
import type { TurnBuilder } from "./turns";
import type { Bytes32, CellId, Effect } from "./internal/wire";
import { fieldFromU64 } from "./internal/wire";
import type { StateConstraint } from "./program";

/**
 * A payment leg to ride alongside a service invocation: pay `amount` of `asset`
 * to the service `provider`. The CALLER pays; this leg desugars to the
 * canonical `Payable` conserving `Effect::Transfer` prepended to the
 * invocation's work, so the payment commits atomically with the call.
 */
export interface PayLeg {
  /** The provider cell that receives the payment (the `to` of the transfer). */
  provider: CellId;
  /** The amount of `asset` to pay. */
  amount: number | bigint;
  /** The asset to pay in (the caller's `token_id`; bridged `$DREGG` is ordinary). */
  asset: Bytes32;
}

/** The cell-field slot the lease durable checkpoint counter lives in (mirrors
 * the Rust `LEASE_STEP_SLOT`; slot 4 is the first general-purpose slot). */
export const LEASE_STEP_SLOT = 4;

/** The default run verb a lease worker is scoped to (mirrors the Rust
 * `DEFAULT_LEASE_METHOD`). */
export const DEFAULT_LEASE_METHOD = "run";

/** The terms a {@link Lease} is opened under. */
export interface LeaseTerms {
  /** The maximum number of durable checkpoints (`run` calls) the lease admits —
   * the capacity tier ceiling the executor binds via `FieldLte`. */
  maxSteps: number;
  /** The lease cell (carrying the checkpoint slot + the meter program). */
  leaseCell: CellId;
  /** The asset the lease cell holds value in (its `token_id`). */
  asset?: Bytes32;
  /** The run verb the lease worker's credential is scoped to. Defaults to
   * {@link DEFAULT_LEASE_METHOD}. */
  method?: string;
}

/**
 * The executor-side meter program a lease cell carries —
 * `FieldLte { step ≤ maxSteps } ∧ Monotonic { step }` on {@link LEASE_STEP_SLOT}.
 * This is the EXACT program the Rust `lease_program` installs and the standalone
 * execution-lease app's `advance_checkpoint` relies on: the `FieldLte` binds the
 * capacity ceiling into every committed transition (a `run` past the ceiling is
 * rejected by the executor) and `Monotonic` forbids rewinding the checkpoint to
 * forge head-room or replay a stale image.
 *
 * Returned as the `StateConstraint[]` that postcard-encodes BYTE-IDENTICALLY to
 * the Rust side, so `program.canonicalProgramVk(leaseProgramConstraints(n))`
 * equals the Rust `canonical_program_vk(lease_program(n))` — a provisioner can
 * install this program and a Rust verifier agrees on its content address. (Pinned
 * in `sdk-ts/test/service-economy.test.mjs`.)
 */
export function leaseProgramConstraints(maxSteps: number): StateConstraint[] {
  const ceiling = maxSteps < 0 ? 0 : maxSteps;
  return [
    { kind: "fieldLte", index: LEASE_STEP_SLOT, value: fieldFromU64(ceiling) },
    { kind: "monotonic", index: LEASE_STEP_SLOT },
  ];
}

/** The outcome of one {@link Lease.run}: the receipt for the metered checkpoint
 * turn, plus the new step index and the steps remaining. */
export interface LeaseStep {
  /** The receipt proving the metered checkpoint turn committed. */
  receipt: Receipt;
  /** The durable checkpoint index AFTER this run. */
  step: number;
  /** How many runs remain on the lease (`maxSteps - step`). */
  remaining: number;
}

/**
 * **A durable, metered execution lease — drive `run` / `fund` against a
 * provisioned lease cell.** The wire twin of the Rust `ExecutionLease`.
 *
 * `run` advances the durable checkpoint (`step → step+1`, a `SetField` the
 * cell's `Monotonic`/`FieldLte` program gates) and meters the workload's
 * effects on the SAME turn — so a workload either commits with an advanced
 * checkpoint or not at all. `fund` moves value into the lease cell with a
 * conserving `Effect::Transfer`.
 */
export class Lease {
  private stepIndex = 0;
  readonly maxSteps: number;
  readonly leaseCell: CellId;
  readonly asset: Bytes32 | undefined;
  readonly method: string;

  constructor(
    private readonly runtime: AgentRuntime,
    terms: LeaseTerms,
  ) {
    this.maxSteps = terms.maxSteps;
    this.leaseCell = terms.leaseCell;
    this.asset = terms.asset;
    this.method = terms.method ?? DEFAULT_LEASE_METHOD;
  }

  /** The durable checkpoint index so far. */
  step(): number {
    return this.stepIndex;
  }

  /** The runs remaining on the lease (`maxSteps - step`). */
  remaining(): number {
    return this.maxSteps - this.stepIndex;
  }

  /**
   * The unsigned-then-signable builder for the next `run`: a
   * `Monotonic`/`FieldLte`-gated `SetField` on {@link LEASE_STEP_SLOT}
   * (`step → step+1`) followed by `work`, on the lease's run verb. Does NOT
   * advance the local counter (inspect / sign without committing).
   */
  runTurn(work: Iterable<Effect> = []): TurnBuilder {
    const next = this.stepIndex + 1;
    return this.runtime
      .turn()
      .on(this.leaseCell)
      .method(this.method)
      .writeU64(LEASE_STEP_SLOT, next)
      .effects(work);
  }

  /**
   * Advance the durable checkpoint and meter `work` on one turn. Submits the
   * {@link runTurn} and, on commit, advances the local step counter.
   */
  async run(work: Iterable<Effect> = []): Promise<LeaseStep> {
    const receipt = await (await this.runTurn(work).sign()).submit();
    this.stepIndex += 1;
    return { receipt, step: this.stepIndex, remaining: this.remaining() };
  }

  /** The signable builder for a funding transfer: one conserving
   * `Effect::Transfer` of `amount` from `funder` into the lease cell. */
  fundTurn(funder: CellId, amount: number | bigint): TurnBuilder {
    return this.runtime.turn().transferFrom(funder, this.leaseCell, amount);
  }

  /** Move `amount` from `funder` into the lease cell with a conserving
   * `Effect::Transfer`. The runtime signs; the executor checks authority over
   * `funder`. */
  async fund(funder: CellId, amount: number | bigint): Promise<Receipt> {
    return (await this.fundTurn(funder, amount).sign()).submit();
  }
}

/**
 * **The service-economy namespace** — `pay`, `invoke`, `lease`. The TS twin of
 * the Rust SDK facade, building the same verified `Action` / `Effect` JSON.
 *
 * ```ts
 * const econ = new ServiceEconomy(runtime);
 * await econ.pay(provider, 1_000n, asset);
 * await econ.invoke(cell, "render", args, { pay: { provider, amount: 250n, asset } });
 * const lease = econ.lease({ maxSteps: 8, leaseCell, asset });
 * await lease.fund(funder, 5_000n);
 * const step = await lease.run(work);
 * ```
 */
export class ServiceEconomy {
  constructor(private readonly runtime: AgentRuntime) {}

  /** The signable builder for {@link pay} (inspect / sign without submitting). */
  payTurn(to: CellId, amount: number | bigint, asset: Bytes32): TurnBuilder {
    return this.runtime.turn().pay(to, amount, asset);
  }

  /**
   * **`pay`** — move `amount` of `asset` from this runtime's cell to `to`
   * through the canonical `Payable` `pay` desugar (one conserving
   * `Effect::Transfer`, per-asset Σδ=0). Byte-identical to the Rust
   * `AgentRuntime::pay`.
   */
  async pay(to: CellId, amount: number | bigint, asset: Bytes32): Promise<Receipt> {
    return (await this.payTurn(to, amount, asset).sign()).submit();
  }

  /**
   * The signable builder for {@link invoke}: an action targeting `cell`'s
   * `method` with `args`, optionally PREPENDING the canonical pay `Transfer`
   * (caller → provider) ahead of `work`. The DFA route + fail-closed
   * unknown-method/under-authority refusals are the node executor's job over
   * the wire.
   */
  invokeTurn(
    cell: CellId,
    method: string,
    args: Bytes32[] = [],
    opts?: { pay?: PayLeg; work?: Iterable<Effect> },
  ): TurnBuilder {
    const builder = this.runtime.turn().on(cell).method(method).args(args);
    if (opts?.pay) {
      // The canonical pay leg: a conserving Transfer caller → provider, ahead
      // of the work — the SAME verified value rail, riding the same turn.
      builder.transferFrom(this.runtime.identity.cellId(), opts.pay.provider, opts.pay.amount);
    }
    if (opts?.work) builder.effects(opts.work);
    return builder;
  }

  /**
   * **`invoke`** — call `method` on the `cell` service, optionally paying
   * through `Payable` in the same turn, and submit. The committed turn carries
   * the routed method + (optionally pay-prepended) effects, mirroring the Rust
   * `AgentRuntime::invoke_service`.
   */
  async invoke(
    cell: CellId,
    method: string,
    args: Bytes32[] = [],
    opts?: { pay?: PayLeg; work?: Iterable<Effect> },
  ): Promise<Receipt> {
    return (await this.invokeTurn(cell, method, args, opts).sign()).submit();
  }

  /**
   * **`lease`** — bind to a provisioned lease cell and drive its durable,
   * metered `run` / `fund` turns. See {@link Lease} and
   * {@link leaseProgramConstraints} for the meter program installed at
   * provisioning.
   */
  lease(terms: LeaseTerms): Lease {
    return new Lease(this.runtime, terms);
  }
}
