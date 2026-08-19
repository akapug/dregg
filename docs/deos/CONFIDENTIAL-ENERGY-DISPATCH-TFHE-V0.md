# Confidential-energy dispatch: exact TFHE candidate validator v0

Date: 2026-08-19  
Status: **MEASURED EXPERIMENT — encrypted candidate validation, not an encrypted solver**

## Verdict

`fhegg-fhe::energy_dispatch` now evaluates an exact bounded arithmetic
projection of `confidential-energy-dispatch/p3-t3-b2-q4/v0` over real tfhe-rs
1.6.3 integer ciphertexts. The evaluator receives a public domain and an
encrypted fixed-shape bundle. It has no `ClientKey` and decrypts no
intermediate value.

Three claims remain separate:

| Predicate | What this backend does | Evidence |
|---|---|---|
| encrypted physical feasibility | Evaluates private provider shape, trajectory, demand, line, and reserve predicates as `FheBool` values | Green for both the cost-56 and feasible cost-60 plans |
| exact settlement conservation | Recomputes encrypted sequential-segment costs and checks provider credits, debit, and objective exactly | Green for honest cost 56 and 60; red for a cost-59 forged settlement over the feasible cost-60 plan |
| global optimality | **Not evaluated**: there is no encrypted search, comparison with all schedules, primal/dual certificate, or proof | The feasible, conserving cost-60 plan stays green for the first two predicates even though the independent Clear oracle finds cost 56 |

Accordingly, `valid_candidate_only` means physical feasibility **and** exact
settlement. It must not be described as a Dark solver, a globally optimal
dispatch, or a proof of correct evaluation.

## Provenance and independent re-specification

The external semantic reference is the prose and relation identifier published
by `degg-research` at commit
`08a0fc357aa32dabf64e2c55f47c33211c148d67`. No source file, Rust module,
fixture, serialized vector, or constant table was imported, linked, generated,
or copied from that repository. This repository contains an independent small
integer re-specification, test instance, Clear test oracle, and encrypted
implementation.

The projection freezes three provider slots, three periods, two buses, two
sequential convex cost segments, and generation atoms `0..=4`. It implements:

- canonical zero padding and bounded occupied provider records;
- private bus, minimum/maximum output, initial output, directional ramps,
  forced-availability bits, segment widths, and nondecreasing marginal costs;
- off-or-minimum output, capacity, pre-horizon and interperiod ramps, with an
  outage boundary bypassing ordinary ramping;
- exact sequential-fill production cost;
- system generation equal to public demand, private-bus line flow equal to the
  claimed offset flow, and public line capacity;
- the frozen upward-capability rule and equality to the claimed reserve;
- exact provider credit equality, credit-sum equality to the debit and claimed
  objective, and equality of that claim to the recomputed objective.

The independently reconstructed regression instance uses the published
cost-56/cost-60 counterexample schedules as externally stated semantic facts,
but chooses and checks its own private provider records and public domain. A
dependency-free `5^9 = 1,953,125` enumeration finds four feasible schedules,
selects the provider-major lexicographically greatest minimum, and reconstructs
the canonical cost 56. Thus the test does not ask the encrypted evaluator to
certify its own optimality claim.

## Boundary and leakage

Clear public evaluator input:

- demand at each bus and period;
- required system reserve per period;
- line capacity per period.

Encrypted client input (63 `FheUint32` ciphertexts including a retained zero):

- 42 provider fields: occupancy, bus, bounds, ramps, initial output,
  availability, segment widths, and marginal costs;
- 20 candidate fields: nine generation atoms, three flow offsets, three reserve
  claims, three provider credits, load debit, and objective claim;
- one encrypted zero used for fixed-shape selections.

The evaluator produces ciphertexts for detailed diagnostics, physical
feasibility, settlement conservation, their candidate-only conjunction, and
the recomputed objective. The benchmark decrypts detailed fields only as a
local diagnostic. A real protocol must freeze and document a narrower leakage
projection; automatically revealing every failed subpredicate and the exact
objective would disclose more than one accept/refuse bit.

The experiment uses a one-process benchmark: the client creates a tfhe-rs
client/server keypair, installs the process-global server key, encrypts, calls
an API that holds no client key, and decrypts diagnostics afterward. Keys are
ephemeral and are neither serialized nor published. The separation illustrates
evaluation-key confidentiality, but it does **not** provide independent or
threshold key custody, selective/threshold result release, malicious-evaluator
security, or a distributed protocol.

The following relation or deployment bindings are deliberately outside this
arithmetic projection:

- provider owner/local-output-recipient bindings and duplicate-owner refusal;
- instance/epoch, accepted-input commitment, and binding ciphertexts to that
  admission commitment or to distinct data owners;
- plan/result/delivery commitments, finality, payload availability, replay,
  consequence, and settlement execution;
- vFHE, a SNARK/STARK/attestation of correct evaluation, evaluator identity, or
  an authenticated transcript;
- global minimum and deterministic equal-cost priority;
- threshold custody, selective output delivery, denial-of-service control,
  and traffic, endpoint, access-pattern, or timing hiding.

FHE answers confidentiality against an evaluator holding only the server key;
it does not by itself answer any of those integrity, custody, liveness, or
optimality questions.

## Measured evidence

Reference host: Apple M2 Max, arm64, macOS Darwin 25.6.0; rustc
`1.98.0-nightly (8b6558a02 2026-06-20)`; tfhe-rs 1.6.3 exact high-level integer
CPU backend; optimized Cargo `release` profile. Wall-clock values are single
runs, not distributional performance claims.

One canonical evaluation:

```text
keygen_ms=607
ciphertexts=63
encrypt_ms=42
witness_checks_ms=8738
trajectory_and_cost_ms=49880
system_checks_ms=24760
settlement_checks_ms=1258
evaluate_total_ms=84638
physical_feasibility=true
settlement_conserves=true
derived_objective=56
global_optimality=NOT_EVALUATED
```

The adversarial three-evaluation gate:

```text
independently_reconstructed_feasible_schedules=4
canonical_cost56: encrypt_ms=44 evaluate_ms=91633 physical=true settlement=true
suboptimal_cost60: encrypt_ms=44 evaluate_ms=97826 physical=true settlement=true
forged_settlement_cost59: encrypt_ms=40 evaluate_ms=89300 physical=true settlement=false
global_optimality=NOT_EVALUATED
whole_test_s=279.54
```

The dominant cost is encrypted trajectory/cost and system arithmetic. This
first experiment intentionally favors an exact legible predicate over a claim
of practical dispatch latency. A future hybrid can keep private arithmetic in
FHE while obtaining optimality from a separately verified certificate, but it
must specify which primal/dual or discrete residual is both sufficient for the
mixed on/off, outage, and deterministic-tie semantics and cryptographically
bound to the same admitted inputs. No such residual is claimed here.

## Reproduction

```sh
cargo check -p fhegg-fhe --features tfhe-integer --test energy_dispatch --bin fhe-energy-dispatch-bench

cargo run --release -p fhegg-fhe --features tfhe-integer \
  --bin fhe-energy-dispatch-bench

cargo nextest run --profile heavy --release -p fhegg-fhe \
  --features tfhe-integer --test energy_dispatch \
  tfhe_validates_feasibility_and_settlement_but_not_global_optimality \
  --no-capture
```

The benchmark emits machine-readable JSON. The adversarial test emits an
`ENERGY_TFHE_MEASUREMENT` JSON record and asserts all three predicate outcomes,
the independently enumerated optimum, and the cost-60 counterexample.
