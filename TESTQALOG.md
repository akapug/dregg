# TESTQALOG — the validation ledger

**APPEND-ONLY. NEVER rewrite or delete another entry — this file is written concurrently by many agents.**
Add your section at the END with a `## <date> — <lane> — <headline>` heading. Cite `file:line`. If you fix
something, say what you fixed and how you VERIFIED it. If you find something you did not fix, NAME it.

---

## The frame (ember, 2026-07-16) — read this before adding anything

> "testing is about **validation**, not verification, you know?"

- **Verification** (the Lean tree) proves *the model we wrote is internally coherent*. It says NOTHING
  about whether the deployed artifact matches that model, or whether the model matches reality.
- **Validation** (this ledger) is the scientific method applied to our correctness ASSUMPTIONS: state the
  assumption, then rig it so **it flags RED if we break it**. That is how a protocol this complex scales
  (ember's years at O(1) Labs on the OCaml integration frameworks — that discipline is why Mina scaled).
- **Dragon's Egg is MORE complex, and AI does not reduce the testing burden. Formal methods do not absolve
  us.** A machine-checked proof of a model is not evidence about the running system.

**ember's honest baseline (do not flatter it):** *"the repo hasn't seen coordinated testing attention from
me in several weeks, so all this stuff is old and extremely underpowered to have confidence in what we have
built."* Expect to find underimplemented, buggy, and sloppy things — in the tests AND in the code they
cover. You are EMPOWERED to make local / mid-scope improvements.

**THE TRAP — do not be deceived by SCALE.** A big test count is not power. Ask of every test: *what real
break would this catch?* Today's proof that scale lies (all found 2026-07-16):
- `tests/src/soundness.rs` — a suite literally named **soundness** was certifying the MOCK IVC. Its
  "tampered hash must fail" passes TRIVIALLY (mutating a field breaks a BLAKE3 digest match). The real
  attack — MINTING a consistent fake — was never tested. It would have passed forever (`61adf7e02`).
- `preflight/checks/*` — the devnet→testnet→mainnet PROMOTION GATE proved SYNTHETIC chains through a mock
  and reported the subsystem GREEN: a gate certifying that the lie is healthy (`e7c692453`).
- **A ratchet that cannot COMPILE cannot bite.** Three gates went silent this way; a non-compiling test
  target is SILENT, not red. It hid a live verify-TCB regression behind 249 un-compiled tests.
- **The root cause**: `.github/workflows/ci.yml` HAS the right gate (`cargo check --workspace
  --all-targets`) — but this clone has NO GitHub remote (only `devnetbox` ssh), so **it never runs here.**
  Guards that never execute are indistinguishable from no guards, except they look protective.

**The questions that matter** (not "how many tests"):
1. What ASSUMPTION does this validate, and would it flag RED if broken?
2. What CONFIGURATION space is never exercised (feature flags, backends, depths, params)?
3. What SCENARIO is never exercised (failure, concurrency, multi-agent, adversarial, recovery)?
4. What COMPOSITION is never exercised (subsystem seams, real e2e flows)?
5. Where do we have VERIFICATION (Lean) but no VALIDATION that the artifact matches it?
6. What is VACUOUS — happy-path-only, tautological, assertion-free, `#[ignore]`d, or unreachable?

---

## 2026-07-16 — Lane 4 (composition / seam coverage) — the PRODUCTION whole-history path (`compress_history`) had ZERO composition tests; the retained-turn→fold seam now has teeth

**The seam map** (flow: turn → circuit → prove → node → wire → lightclient/grain-verify), ranked by
composition risk. "Covered" means at least one test drives REAL artifacts across the seam.

1. **node retention → IVC fold → light-client verify: WAS ZERO — FIXED.** The production
   whole-history path is `node/src/mcp/handlers_verify.rs:62` (`tool_compress_history`): load retained
   envelopes from the config store → `decode_retained_finalized_turn` (`node/src/turn_proving.rs:1616`)
   → `prove_turn_chain_recursive` → `verify_whole_chain_proof_bytes` (the light-client teeth). **No test
   in the repo referenced `compress_history` at all** (grep: only the 5 src files). The two sides were
   tested only separately: node side, ONE turn's retention round-trip stopping at host admission
   (`turn_proving.rs:1747`); fold/light-client side, chains minted DIRECTLY from fixtures via
   `mint_rotated_participant_leg` (`grain-verify/tests/r3_whole_history.rs:66`, `lightclient/src/lib.rs:1211`,
   `lightclient/src/bin/whole_history_demo.rs`) — never through the node's retention encode/decode. So the
   fold's temporal tooth (`new_root[i] == old_root[i+1]`, `circuit-prove/src/ivc_turn_chain.rs:1714`) was
   never checked across CONSECUTIVE node-retained turns — the exact property whose absence previously made
   whole-history proving impossible (the node used to retain only hashes). State-threading, retention-mint,
   or registry-row descriptor-rebuild drift would keep every per-side test green while
   `dregg_compress_history` failed on every real node.
2. **live node with proving ON → store retention: STILL UNCOVERED (named, not fixed).**
   `full_turn_proving_enabled` is false by default (`node/src/state.rs:952`), enabled only by
   `--prove-turns`/`DREGG_PROVE_TURNS=1` (`node/src/lib.rs:1469`). NO node integration test boots a node
   with it on — `node/tests/payoff_client_turn.rs` (the 4-node consensus payoff) finalizes turns with
   proving OFF, so the `blocklace_sync::execute_finalized_turn` proving+retention branch
   (`node/src/blocklace_sync.rs:5038`) never executes under test on a running node. Only shell smoke
   scripts set it, and `scripts/smoke-cli-turn.sh:191` accepts `proof_status in ("proved","not_required")`
   — with DREGG_PROVE_TURNS=1 a silently-skipped prove still passes GREEN, and the script never checks
   the retained `finalized_turn:` envelope exists.
3. **bridge action → settled:** real ungated mechanism tests exist (`bridge/tests/committed_double_mint.rs`,
   `solana_consensus_mint.rs`, relayer roundtrips); the actual settle legs are env-gated live tests
   (`bridge/tests/solana_local_e2e.rs:73` needs `SOLANA_LOCAL` + artifacts; devnet/midnight similar) —
   structural, but note they never run unprompted. The note-spend/bridge binding teeth in circuit-prove are
   honestly labeled MECHANISM (not deployed-VK) teeth (`circuit-prove/tests/note_spend_binding_node_tooth.rs:20`).
4. **presentation issued → verified:** covered with real STARKs in `tests/src/full_pipeline.rs` (Tests 1–2);
   `bridge/tests/integration_present_credential.rs:11` is `prove_fast()`-only (constraint-check, no STARK) —
   acceptable as a fast tier only because full_pipeline backs it.
5. **turn → circuit → prove → per-turn node commit:** well covered with real artifacts
   (`node/src/turn_proving.rs` 34 tests incl. freshness/cap/bearer anti-ghosts; circuit-prove emit gates).
6. **node → wire → external client:** covered (`node/tests/payoff_client_turn.rs` real 4-node HTTP+QUIC
   consensus; `wire/tests/integration_gossip_attested_root.rs`) — but see item 2: never WITH proving.
7. **note spend → nullified:** covered at SDK + node-function level (`turn_proving.rs:2555–2892`, honest/
   wrong-root/wrong-item/double-spend), with the honest 14-entry capacity bound documented at
   `turn_proving.rs:1` — but never on a running node (item 2 again), and `grain-verify`/`lightclient`
   whole-history tests all run empty nullifier/commitments roots.

**FIXED — new composition test: `node/tests/retained_history_ivc_seam.rs`** (real artifacts through
node → circuit-prove → light-client verifier):
- `retained_consecutive_turns_chain_for_the_fold` (default-run, PASSED in 247s): two CONSECUTIVE turns
  proven + retained + decoded exactly the commit path's way (`prove_and_verify_finalized_turn` →
  `mint_and_encode_finalized_turn` → `decode_retained_finalized_turn`), then asserts (a) both decoded legs
  pass the fold's host admission, (b) decoded anchors == the served proofs' anchors (retention/registry
  drift flags RED), (c) THE TEMPORAL TOOTH across the seam: `new_root[1] == old_root[2]` on all 8 lanes,
  (d) discriminating power: a STALE-threaded turn (re-proven from turn 1's pre-state — the state-threading
  bug class) has `old_root == turn1.old_root` but `!= turn1.new_root`, so (c) cannot pass vacuously.
- `retained_history_folds_and_verifies_like_compress_history` (#[ignore], SLOW — real recursion; PASSED
  in 307s via `-- --ignored`): the decoded node-retained turns drive the REAL
  `prove_turn_chain_recursive` fold, the byte envelope re-verifies through `verify_whole_chain_proof_bytes`
  against the recomputed VK fingerprint (the SAME teeth `tool_compress_history` runs), and the
  stale-threaded chain is REFUSED by the fold. First time the production compress path's exact composition
  has ever executed under test.
- Verified: `cargo test -p dregg-node --test retained_history_ivc_seam` → ok (1 passed, 1 ignored);
  `... -- --ignored` → ok (1 passed). Bites: the in-test stale-thread `assert_ne` + fold refusal prove the
  chain equalities/fold acceptance are not tautologies.

**NOT fixed (named):** (i) no test boots a live node with `DREGG_PROVE_TURNS=1` and asserts a finalized
turn leaves a `finalized_turn:<hash>` envelope in the store — the retention CALL SITE in blocklace_sync is
still never executed under test (my test drives the same functions directly, not the running-node branch);
(ii) `scripts/smoke-cli-turn.sh:191`'s soft `not_required` acceptance under proving; (iii) an MCP-level test
of `tool_compress_history` itself (store keys, fail-closed missing-turn path — the error paths at
handlers_verify.rs:112–134 are untested); (iv) bridge live-settle legs remain opt-in env-gated.

**In-flux note:** other lanes hold edits in `node/src/mcp/handlers_verify.rs`, `node/src/lib.rs`,
`tests/src/*`, `circuit-prove/*` — read but not touched (one `cargo fmt -p dregg-node` normalized
whitespace crate-wide; semantics untouched). My change is the ONE new file above.

## 2026-07-16 — mocks-mirrors-fakes/deos-agents — dregg-tui's "Verify" tab walked the operator through a step 3 that never ran

**CONFIRMED (THEATER, HIGH).** `dregg-tui`'s headline Verify tab — the interactive `[v]` key
(`App::verify_selected`) and the `--verify-head` headless CLI — gated its `✓ INDEPENDENTLY VERIFIED` /
`✗ NOT VERIFIED` badge on `dregg_verifier::verify_effect_vm_proof`. That function is RETIRED
(`verifier/src/lib.rs:155-169`): it discards `proof_bytes` / `public_inputs_u32` / `vk_hash_hex` and
returns a fixed rejection on every build. Read from code, not comments — the verifier crate is HONEST
(it fails closed and says so); the LIE lived entirely in the TUI wrapped around it. The module doc
(lines 1-33), the `Cargo.toml` dep comment, and the in-UI text all claimed step 3 ran "the REAL plonky3
STARK verifier … the verbatim verify core the seL4 M-STARK / M1 verifier PDs boot" and that "the proof
either verifies under the audited AIR or it does not."

What an operator actually saw: three convincing steps, then `REJECTED (exit 2)` and
`RESULT: NOT VERIFIED`, exit 1 — for every receipt, valid or forged. The deception ran in the
UNUSUAL direction (never a false pass, always a false FAIL), which is why it survived: nothing
looked "too green". It still reported a cryptographic verdict on a proof nothing had read, and
`--verify-head`'s exit 1 told any script "this proof is bad" when the truth was "no verify core
exists here". The TUI's own `run_selfcheck` already knew the v1 core was retired; that knowledge was
never propagated to `verify_receipt`, the function the shipped keybinding calls.

**Fix — HONEST FAIL-CLOSED (option 3), because the rewire is a DESIGN DECISION, not a typo.**
Rewire to a real counterpart was investigated and REFUTED as available at this layer:
* `verify_rotated_replay_chain` wants `RotatedReplayLeg{Ir2BatchProof, public_inputs, vk_hash}`; a
  `WitnessedReceipt` carries neither an `Ir2BatchProof` nor a `vk_hash`. Its own module doc calls it
  the CLI/demonstration floor, explicitly "NOT the deployed sovereign turn-verify wire".
* The node's producers (`node/src/prove_pool.rs:232`, `node/src/api.rs:8832`) build the WR with
  `proof_bytes = FullTurnProof::proof_bytes` = a postcard `ComposedProof`. Its real verify IS
  `dregg_sdk::verify_full_turn_bound` — but nothing in the tree decodes a `WitnessedReceipt` back
  into a `FullTurnProof` (`TurnProofComponents` / `turn_hash` are not in the serialized
  `ComposedProof`), and `verify_full_turn_bound` is called from NOWHERE outside `sdk/tests/*`.

`verify_receipt` now returns a three-state `VerifyOutcome` — `Verified` / `Rejected` / `Unavailable`
— deliberately NOT a bool. `Unavailable` is not `Rejected`: collapsing them is what told operators a
proof had failed. Steps 1-2 (fetch, canonical DWR1 decode, receipt-hash binding re-check) still do
their real work and a swapped artifact is still a real `Rejected`. Step 3 no longer invokes the
retired core on the receipt's proof at all; it reports `⚠ CANNOT VERIFY HERE — NO VERDICT` and names
the three missing pieces. `--verify-head` now exits 2 (no verdict), kept distinct from 1 (rejected).

**Teeth — PROVEN TO BITE, not self-reported.** Two tests in `dregg-tui/src/main.rs` drive the SHIPPED
`verify_receipt` over real HTTP against a stub node serving a REAL DWR1 artifact (encoded by the
node's own `WitnessedReceipt::to_artifact_bytes`), so steps 1-2 do real work:
* `unwired_verify_core_yields_no_verdict` — the proof nothing examined must yield `Unavailable`.
  **Injected the exact historical lie** (step 3 returning `Verified`) and watched it FAIL:
  `panicked at src/main.rs:1092: step 3 is not wired: a proof nothing examined must yield NO VERDICT,
  not a pass and not a rejection`. Reverted → green.
* `receipt_hash_mismatch_is_a_rejection_not_a_shrug` — a real break this client detects ITSELF must
  stay `Rejected`, so the not-wired state cannot swallow a genuine detection.

This test is the standing record that step 3 is a hole: whoever wires a real core will see it FAIL,
which is the correct alarm — it must be deleted by the same change that fills the hole.
Also drove the real binary end-to-end (`cargo run -- http://127.0.0.1:8791 --verify-head` against a
stub node): prints `NO VERDICT — this client did not verify the proof. This is NOT a statement that
the proof is bad.`, exit 2. `cargo test -p dregg-circuit-prove --test mock_proof_purge_gate` ok
(baseline untouched, not lowered — dregg-tui rides no mock prover; it rode a retired one).

**NAMED, not fixed (the rewire needs decisions I cannot make):**
(i) **No trusted endpoints.** `verify_full_turn_bound` takes the `expected_old_commit` /
`expected_new_commit` / `expected_revocation_root` the verifier TRUSTS. A light client with only this
node's HTTP API has no authenticated source for them — taking them from the proof's own PI would make
the check circular and worthless. This is the real reason the TUI cannot verify, and it is an
architecture question (what does a light client anchor to?), not a wiring bug.
(ii) **No decoder.** A public SDK entry from `WitnessedReceipt.proof_bytes` → `FullTurnProof` must be
authored, and it must decide where `components` / `turn_hash` come from.
(iii) **Feature reach.** dregg-tui pulls `dregg-sdk` with `default-features = false`, so `prover` is
off and the `"effect-vm-rotated"` arm of `verify_full_turn_bound` — the arm every live leg needs — is
compiled out. Turning `prover` on drags the prover into the light client, against the verifier-floor
design. This is the same shape as the `verifier` crate's prover-free floor decision.
(iv) `dregg-tui`'s `dregg-circuit` + `dregg-turn` deps are now DEAD in `src/main.rs` (their comment
still described a `--selfcheck` that proved a fresh turn; `run_selfcheck` now only prints the
retirement). Left in place with an honest STALE comment: removing a dep rewrites
`dregg-tui/Cargo.lock`, which another lane holds dirty. (`dregg-turn` is used by my new tests, so
only `dregg-circuit` is fully dead.)

**In-flux / skipped as dirty:** `dregg-tui/Cargo.lock` (dirty on arrival — not touched; only comments
were edited in `Cargo.toml` so no re-resolve). **Live red umbrella observed and NOT touched:** a lane
deepened `FoldDelta::apply_and_verify` in `commit/src/fold.rs` (dirty) from 0 args to
`(&TokenState, &CheckPolicy)`; its CLEAN downstream consumer `bridge/src/present.rs:777` and
`commit/src/fold.rs`'s own `#[cfg(test)]` mod went red, which blocked the whole dregg-tui dep graph
for ~2 min until that lane landed the fix. Reported, not fixed — but it is the exact "per-file green
hides a red umbrella" failure, caught live.

## 2026-07-16 — mocks-mirrors-fakes/harnesses — the Lean faithfulness gate could not be red; armed it

**Fixed — THEATER, `preflight/src/checks/lean_marshal.rs`.** `check_marshal_roundtrip` returned
`Ok(())` whenever `dregg-lean-ffi/libdregg_lean.a` was absent. `PreflightReport` has no Skipped
state (`report.rs:24-34,123-140`: `passed=true` on `Ok(())`; `all_passed()`/`passed_count()` cannot
tell a skip from a pass), so that silent `Ok(())` fed the same tally as every real check, and the
same banner: `PREFLIGHT PASSED: N/N checks ... Ready for testnet promotion.` (`report.rs:98-106`,
`main.rs:65-67`, `#[test] preflight_golden_master` at `main.rs:220-239`). The one gate standing
between promotion and an undetected Lean<->Rust executor divergence reported the same green whether
the executors agree or whether nobody looked.

**The fix was a REWIRE, not new machinery — the honest failure already existed and the caller was
declining to use it.** `scripts/check-lean-marshal.sh` already documents its own skip as a lie
("THE SKIP IS A LIE DETECTOR, NOT A PASS ... NOTHING WAS CHECKED ... a checkmark that is
structurally incapable of being red") and already ships `DREGG_REQUIRE_LEAN_GATE=1` to turn an
absent archive into a nonzero exit naming exactly what is missing. `ci.yml` arms it; preflight did
not — and worse, preflight pre-empted the script with its *own* `is_file()` skip, so the script's
honest branch was unreachable from the promotion gate. Deleted the pre-emptive skip (and the now-dead
`lean_lib_path()`; no other refs) and pass `.env("DREGG_REQUIRE_LEAN_GATE", "1")`. The script stays
the single source of truth for what "the Lean gate passed" means. This matches the pattern the crate
already states for itself in `checks/demo_agent.rs:28-31` — "green-or-bust: a skipped example is a
failing example; there are no non-fatal skips" — which `lean_marshal.rs` alone inverted.

**PROVED THE TOOTH BITES (differential, not assertion).** The archive is present on this box (106 MB),
so moving it to force a red was unsafe in a shared tree — other lanes link it concurrently. Instead
ran the script against a scratch root with no archive: **UNARMED (old preflight behavior) => exit 0,
"SKIP — NOTHING WAS CHECKED"** (a full PASS in the tally); **ARMED (new behavior) => exit 1**, stderr
naming the missing archive => `CheckResult.passed=false` => banner flips to `PREFLIGHT FAILED`.
`cargo build -p dregg-preflight` green with the change; zero warnings from `preflight/src`.

**Refuted nothing outright, but SCOPED DOWN candidate 1** (`check_ivc_proof` / `check_ivc_chain` /
`check_ivc_recursive` consuming the known-mock `verify_ivc`). Confirmed from code, NOT refuted:
`circuit/src/ivc.rs:958-991` recomputes a BLAKE3 digest over fields read off the SAME `IvcProof`
being checked and compares it to `proof.proof.trace_digest` written by the same `prove_ivc` — anyone
who can call `prove_ivc` mints a passing proof for any root walk; `ivc.rs:30-37` says so itself
("Without the real recursion backend, the IVC is implemented as a HASH CHAIN"). **Not fixed: all
three sites were dirty on arrival** (`preflight/src/checks/{proofs,composition,backends}.rs`, plus
`checks/mod.rs`) and are contested. Reported to the supervisor, not edited.

**NAMED (needs a decision I cannot make):** the promotion gate presents a self-referential hash check
as folding/recursion soundness under the names `ivc`, `chain`, and `ivc-recursive`. Until the Plonky3
recursive verifier lands, those three either get renamed to non-cryptographic bookkeeping smoke tests
or leave the tally that prints "Ready for testnet promotion." Renaming is cosmetic; **excluding them
shrinks the gate**. That is ember's call, not a lane's.

**Environment note:** the workspace disk hit 100% (197 Mi free) mid-run — a later rebuild died with
`No space left on device`. Not caused by this change (the clean build predates it), but it will
break other lanes.

---

## 2026-07-16 — Lane 5 — THE ASSUMPTION LEDGER: the crypto floor's two load-bearing constants were prose

**The frame applied.** An assumption is only rigged if a test flags RED when the code drifts from it.
I walked the assumption surface (Lean `#assert_axioms` carriers, named residuals, `SAFETY:`/`INVARIANT:`
comments, descriptor pins) hunting the specific pathology the lane names: **assumptions CHECKABLE in
Rust but asserted only in PROSE**. The worst two sit at the bottom of the Schnorr curve stack, where
everything above them is a corollary.

### THE HEADLINE: a test named `is_a_field_no_zero_divisors` cannot detect that it is not a field

`circuit/src/babybear8.rs` builds `F_p[z]/(z^8 - 11)` and its header (lines 4-20) narrates, at length,
a REAL historical bug: the old tower reused the non-residue `11` at both layers, so `y^2 - 11` factored
and the quotient was the **product ring** `F_{p^4} × F_{p^4}` with zero divisors. The fix — extend by a
genuine degree-8 irreducible — rests entirely on the assumption **`z^8 - 11` is irreducible over
BabyBear**, sourced to a parenthetical: *"(verified: it factors as a single degree-8 irreducible)"*.
No test checked it.

I asked the lane's question — *what real break would the existing tests catch?* — and answered it by
**exact simulation** (scratchpad `bb8sim.py`, a faithful mirror of `mul`/`inverse`/`pow_multi`
parameterised by the non-residue `W`). Sabotage `W: 11 → 121` (`z^8-121 = (z^4-11)(z^4+11)` — the
historical product-ring shape, reachable by a **one-character edit**):

| existing test (`babybear8.rs`) | verdict under `W = 121` (the broken product ring) |
|---|---|
| `is_a_field_no_zero_divisors` :437 | **PASS** |
| `frobenius_order_eight` :655 | **PASS** |
| `defining_relation_z8_eq_w` | **PASS** |

Every test green on a ring with zero divisors. The reason is the lane's thesis in miniature: the
2000-element sweep looks for zero divisors **at random**, and in `F_{p^4} × F_{p^4}` a random element
is a unit with probability `(1 - p^-4)²` — the zero divisors are a measure-`~p^-4` sliver that a sweep
will never hit. Its hardcoded `A = z - z^4` witness is basis-specific to the OLD tower and is a unit in
both rings. `frobenius_order_eight` checks `a^(p^8) = a`, which holds in the product ring too (each
component is `F_{p^4}`, and `p^4 | p^8`). **The test suite could not detect its own documented bug.**

**FIXED — rigged as an algebraic invariant, which does not hide:**
- `circuit/src/babybear8.rs:492` `irreducibility_frobenius_orbit_of_z_is_exactly_eight` — `z^8-W` is
  irreducible **iff** the Frobenius orbit of `z` has size exactly 8: `z^(p^8) = z` AND `z^(p^d) ≠ z`
  for every proper divisor `d ∈ {1,2,4}`. Under `W=121`, `z^(p^4) = z` and this fires.
- `circuit/src/babybear8.rs:552` `irreducibility_gate_is_non_vacuous_it_fails_on_the_product_ring` —
  **proof the gate can go red, shipped as a test.** `W` is a private const, so rather than mutate
  shared source I mirror the arithmetic W-parameterised, assert the mirror is **faithful** to the
  deployed `BabyBear8` at `W=11`, then require the orbit predicate to PASS at `W=11` and **FAIL** at
  `W=121`. The gate is proven discriminating in-tree, permanently — not in a scratchpad that rots.

### #2: `N` prime was a PARI run recorded in a comment

`circuit/src/schnorr_curve.rs:122` pins the 248-bit group order `N`; the header (lines 19-24) claims
prime order, cofactor 1, *"(Verified: `isprime(N)`, `ellcard(E) == N`, cofactor `== 1`.)"* — a PARI
session no test reproduces. **Primality is load-bearing twice over**: it is the DL hardness the curve
rests on, AND it is the hidden premise of `generator_cofactor_is_one` :996, whose argument is "the
order divides the prime `N` and is not 1, therefore equals `N`". If `N = a·b`, the generator could have
order `a` — and `generator_has_order_n` :983 (`N·G = O`) **still passes**, because `a | N`. The cofactor
argument collapses silently and both existing tests stay green. This is not hypothetical: the module
header (line 30) records the retired base-field curve whose order was the composite
`2013191319 = 3·331·2027383`, *"trivially broken"*.

**FIXED:**
- `schnorr_curve.rs:695` `order_is_prime_miller_rabin` — a Miller–Rabin strong-probable-prime gate on
  the pinned `ORDER`, over an **independent** modulus-parameterised bigint, deliberately NOT built on
  `scalar_mul_mod` (which is hard-wired to `ORDER`) so a bug in the deployed scalar arithmetic cannot
  mask a composite constant.
- `schnorr_curve.rs:714` `primality_gate_is_non_vacuous_it_rejects_composites` — the tooth: it must
  reject `2013191319` (the actual retired composite order — the exact regression the gate exists for),
  and the Carmichael numbers 561/1105/1729/2465.
- `schnorr_curve.rs:637` `order_limbs_equal_documented_decimal` — the 8 hand-authored u32 limbs are
  nailed to the documented decimal by long division. A limb slip silently changes the group order.
- `schnorr_curve.rs:759` `independent_mul_mod_agrees_with_deployed_scalar_mul_mod` — differential
  fallout: two independent implementations must agree mod `ORDER`. Real evidence about the arithmetic
  carrying every Schnorr response `s = k - e·sk`.

**A gate I wrote and then had to throw away — recorded because it is the lane's lesson.** My first
primality gate was a **Fermat** base-2 witness, and I wrote a control asserting it rejects the
Carmichael numbers. It does not: `2^560 ≡ 1 (mod 561)` — Carmichael numbers pass Fermat *by
definition*, which is what they are. My control was WRONG and would have failed. Checking it before
shipping is what upgraded the gate to Miller–Rabin. **A Fermat gate here would have waved through any
Carmichael substitution while looking exactly as protective.** The non-vacuity control did not just
document the gate — it repaired it.

### FIXED (code, not test): an ed25519 verification drifted off the repo's own contract

`token/src/revocation.rs:353` verified the classical half of a hybrid revocation attestation with
non-strict `vk.verify(...)`. **Every other ed25519 site in the tree is strict** —
`sel4/dregg-pd/executor-pd/crypto-floor/src/ed25519.rs:6` documents `verify_strict` as *"the exact
contract"*, and `lightclient/src/lib.rs:389`, `cell-crypto/src/capability_proof.rs:529` follow it.
Non-strict `verify` is cofactored and accepts small-order public keys, under which `(R = s·B, s)`
verifies for **every** message — a universal forgery of the classical half. It also disagrees with the
scheme the Lean models: `Ed25519EufCma` (`metatheory/Dregg2/Crypto/Ed25519Reduction.lean:16`) closes
over the STRICT primitive, so this site was verified against a model of a different scheme.
Now `verify_strict`. Verified: `cargo test -p dregg-token --lib -- revocation` → **23 passed, 0
failed**, including the 6 `verify_hybrid` teeth.

**Honest bound on that one — do not let it read as a save.** The authority key is enrolled and pinned
(`revocation.rs:330`) and the ML-DSA half still gates, so I could not construct a reachable exploit;
the consequence is DEFENSE-IN-DEPTH and model-fidelity, not a live hole. **I did NOT rig a test that
distinguishes strict from non-strict**, because at `verify_hybrid`'s altitude the only way to reach the
difference is an attacker-chosen enrolled authority key — at which point the PQ half is attacker-chosen
too and the threat model is already lost. A test asserting `verify_hybrid` rejects there would pass for
the wrong reason and be exactly the vacuous tooth this log exists to hunt. **The drift is fixed; it is
not rigged.** Rigging it properly means a primitive-level check that no ed25519 call site in the tree
uses non-strict `verify` — a grep-shaped lint, and the right fix, which I did not build.

### THE UNRIGGED, RANKED BY CONSEQUENCE (what I did NOT fix)

1. **`descriptor_sha256` (75 pins) in `circuit/descriptors/PROVENANCE.json` is checked by NO Rust
   test.** `scripts/check-descriptor-drift.sh` is the honest gate (it RE-DERIVES from Lean rather than
   rehashing, and its own header explains why a rehash proves nothing) — but it needs a Lean toolchain
   and runs only from `.github/workflows/ci.yml:417`. **Correction to this log's frame:** this clone
   DOES have a GitHub `origin` (`git@github.com:emberian/dregg.git`), so the earlier "no GitHub remote,
   it never runs" claim is not true as written here. Whether that workflow actually executes on push I
   could not confirm from inside the clone — and *that* is the assumption worth rigging: nothing local
   proves the descriptors match the Lean. The installed hooks (`pre-commit`, `pre-push`) gate rustfmt
   and secret-scan only — no drift check, no `cargo check --workspace --all-targets`.
2. **`Ed25519EufCma` / `SchnorrDLHard` / `ForkingExtractor` — the irreducible carriers.** Correctly
   irreducible (a Prop whose negation is a concrete solver, `:= True` avoided — the discipline is real
   and good). Unrigged and largely unriggable by test; the validation question is not "is DL hard" but
   **"does the deployed Rust implement the scheme the carrier is about"** — which is exactly the gap
   the `verify_strict` drift above was sitting in. That class deserves a systematic sweep: for each
   named carrier, one test that the artifact matches the modelled scheme. I did one site by hand.
3. **`schnorr_curve.rs` curve params `a`, `b`, and `GENERATOR`** — `#E(F_{p^8}) = N` (the SEA
   point-count) is still prose. `generator_has_order_n` :983 pins `G` to `N`, and `is_on_curve` covers
   `a`/`b`, so the residual is narrower than primality was: nothing checks that `N` is the FULL curve
   order rather than the order of `G`'s subgroup. Cofactor-1 is only *inferred* (now soundly, given the
   primality gate). Genuinely hard to test in Rust — it wants the Lean/PARI rail.
4. **`CurvePoint::new` does not check `is_on_curve`** (`schnorr_curve.rs:147`, comment says so
   plainly), and `schnorr_verify` (`schnorr_sig.rs:133`) rejects only the identity — **not** off-curve
   public keys. The add/double formulas never read `b`, so an off-curve point lives on a *different*
   curve and the group law is closed there: the classic invalid-curve setup. I did not find a reachable
   exploit (verify's `e·pk` uses a public scalar, and no secret is multiplied by an attacker-supplied
   point), so I did not rig it — but any future path that multiplies a SECRET by a caller-supplied
   point makes this live. **Name it before that path exists**, not after.

**Not fixed, environment:** the workspace disk hit 100% mid-session and blocked all builds for a
stretch (another lane logged it too). My circuit gates were verified green **before** it, and the token
run after space freed; but the 249-target `cargo check --workspace --all-targets` that would prove no
silent-ratchet regression is unrun by me.

**Verification of this entry's claims:** `cargo test -p dregg-circuit --lib -- babybear8::tests
schnorr_curve::tests` → **49 passed, 0 failed** (5 new: 2 gates + 2 non-vacuity controls + 1
differential; no regressions). `cargo test -p dregg-token --lib -- revocation` → **23 passed, 0
failed**. The product-ring blindness of the pre-existing tests is not an opinion — it is the exact
simulation in the table above, reproducible from `bb8sim.py`.

## 2026-07-16 — Lane 3 (scenario / failure / adversarial) — a fail-closed guard that never compiled, and a gate named `peer_exchange` that never ran peer exchange

**Headline:** the lane brief named `verify_stark_transition` as a guard with no test. It is worse than
untested. `cell-crypto/src/peer_exchange.rs:312` gated it `#[cfg(feature = "zkvm")]` — and
`cell-crypto/Cargo.toml` **has no `[features]` section at all**. The gate compiled to *nothing* in
every build, so a peer transition carrying a v1 `transition_proof` was **silently ACCEPTED**. The
doc directly above it claimed it "fails closed." It failed **open**. Fixed + tested.

### 1. FIXED — peer_exchange rule 5 was fail-OPEN while its doc claimed fail-closed

- `cell-crypto/src/peer_exchange.rs:312` — `#[cfg(feature = "zkvm")]` in a crate with zero declared
  features. Dead gate. `transition_proof: Some(..)` → ignored → `Ok(())`.
- The **executor sibling** gate (`turn/src/executor/execute.rs:940`, sovereign-witness rule 8) is
  unconditional and *rejects*. So the two verify paths **disagreed** on the same retired-v1 contract:
  the executor refused it, peer_exchange waved it through. (THE SWAP shape: dual impls, one silently
  weaker.)
- Aggravator: `canonical_message` (`peer_exchange.rs:417`) covers only
  `old||new||effects_hash||ts||seq` — **not** `transition_proof`. The field is wire-malleable: an
  active attacker attaches/strips it and the Ed25519 signature stays valid. Nothing but rule 5 stops it.
- **Fix**: guard made unconditional (`peer_exchange.rs:312-328`), matching the executor. Deleted the
  two now-dead `zkvm`-gated helpers (`verify_stark_transition`, `commitment_to_4bb` — the latter
  entirely unreachable; the live `commitment_to_4bb` is the unrelated one in
  `turn/src/executor/proof_verify.rs:2901`). Corrected the three doc comments that described the
  phantom config (field doc `:47`, `verify_transition` doc `:255`).
- **Test that bites**: `peer_exchange.rs:669 peer_transition_carrying_v1_stark_proof_rejected`. It
  carries a **control leg** — the byte-identical transition with the proof removed *verifies OK* —
  so the reject is provably caused by the proof field alone. Pre-fix this test FAILS (the gated block
  did not exist; control flow fell straight through to `Ok(())`). Verified: `cargo test -p
  dregg-cell-crypto --lib peer_exchange` → **8 passed**.

### 2. ROOT CAUSE (systemic, NOT fixed) — `unexpected_cfgs = "allow"` silences phantom gates workspace-wide

`Cargo.toml:322` — the **only** entry under `[workspace.lints.rust]` — is
`unexpected_cfgs = "allow"`. That is precisely the lint that flags a `cfg(feature = "x")` whose crate
never declares `x`. It is disabled across all ~201 crates, which is why the fail-open above compiled
clean and silent for however long it has been there. Nothing is red; nothing was ever going to be red.

This repo already **paid for this lesson and wrote it down**: `tests/Cargo.toml:19-24` documents, in
prose, that "a bare `cfg(feature = "prover")` here is ALWAYS false (the crate has no such feature)."
They hit it, diagnosed it, fixed that one instance — and left the lint that finds the *rest* off.

I swept the workspace for it (script in scratch). The raw grep flags ~17 sites across 8 crates, but
most are false positives once you exclude gates inside doc-comments / `//` comments (`circuit-prove
lib.rs:17`, `bridge present.rs:91`, `sdk privacy.rs:1088`) and gates emitted into *consumer* crates
from inside a `quote!{}` macro body (`dregg-dsl gen_plonky3.rs` ×3 — evaluated against the consumer's
features, not dregg-dsl's). After filtering, the genuinely in-effect phantom gates are **11 sites
across 4 crates**:
- `cell-crypto` `zkvm` ×3 — **FIXED above.**
- `dregg-sdk-net` `reqwest` ×3 — real and harmful, see below.
- `dregg-turn` `verifier` ×3 — real but currently benign, see below.
- `starbridge-v2` `zed-full-pane` ×2 — `zed_full_pane.rs:53` is `#![cfg(feature = "zed-full-pane")]`
  at MODULE scope, but `starbridge-v2` declares no such feature — the whole module never compiles.
  Possibly deliberate dead-coding (a separate `deos-zed-full` crate exists), but if so it is dead by
  accident of a misspelled gate, not by intent. Flagged, not touched.

The two that matter beyond style:

- **`dregg-sdk-net/src/discovery.rs:71,76,85`** — `ReqwestTransport`, whose own doc says *"This is
  the production transport"*, is gated `#[cfg(feature = "reqwest")]`. `reqwest` is a **non-optional
  dependency** (`dregg-sdk-net/Cargo.toml:52`) and there is **no `reqwest` feature**. The production
  PIR discovery transport is **compiled out of every build**; the only surviving `PirTransport` impls
  are test/mock ones. Following the module's own example (`discovery.rs:150`) yields a compile error.
  NOT FIXED (needs an owner call: delete the gates vs. add the feature).
- **`turn/src/bilateral_schedule.rs:733,813`, `turn/src/witnessed_receipt.rs:542`** —
  `cfg(any(feature = "prover", feature = "verifier"))`; `dregg-turn` declares only `prover` and
  `threshold-sig` (`turn/Cargo.toml`). No `verifier`, no `recursion`. Currently benign *only* because
  `prover` is in the default set — but the intended verify-only / wasm config
  (`default-features = false` + verifier) silently loses those functions instead of failing. A
  config-space hole (frame question #2), latent rather than live.

Flipping `unexpected_cfgs` to `"warn"` surfaces all 17. I did not flip it — it is a workspace-wide
call with a blast radius past my lane, and two lanes are mid-flight in this tree.

### 3. FIXED — executor rules 7 & 8 had no red-flag test; the suite's own helper made 7b untrippable

`tests/src/sovereign_witness_threats.rs` is a genuinely strong suite (replay, cross-cell reuse, key
rotation, equal-sequence, cross-federation replay all bite). But **every** witness in it is minted by
`signed_sovereign_witness_with_new_commitment`, which (a) hard-codes `transition_proof: None` and
(b) **coerces an all-zero `effects_hash` into a non-zero hash** (`:248-252`). So three unconditional
`return TurnResult::Rejected` guards in `execute.rs` were structurally unreachable from this suite —
deleting any of them broke no test. The helper's own doc comment cites "execute.rs rules 7/8" while
guaranteeing they can never fire.

Added `raw_sovereign_witness` (`:1076`, signs correctly, passes fields through verbatim, attaches the
proof *after* signing — faithful, since the signing message does not cover it) plus:

- **`:1126 sovereign_witness_carrying_v1_transition_proof_fails_closed`** — rule 8
  (`execute.rs:940`). **No prior test existed.** Highest blast radius here: the witness is otherwise
  perfect, and the control leg proves the identical witness **commits** once the proof is dropped —
  so rule 8 is the only thing between an unverified 4 KiB blob and a committed sovereign transition.
- **`:1246 sovereign_witness_zero_effects_hash_placeholder_rejects`** — rule 7b (`execute.rs:926`).
  **First test to reach it.** `turn/src/tests.rs:6996` sets *both* zeros, so rule 7a short-circuits
  and 7b is never evaluated; no test asserted its message. Mine passes a valid `new_commitment` so 7b
  fires alone.
- **`:1197 sovereign_witness_zero_new_commitment_placeholder_rejects`** — rule 7a. Partial prior
  coverage at `turn/src/tests.rs:6996`; mine isolates 7a (valid effects_hash) and adds the
  replay-sequence-non-advancement assert.

All three assert the **specific** rejection reason, not `is_rejected()` — deleting a guard changes
the reason (7a → `SovereignCommitmentMismatch`, 7b → `EffectsHashMismatch`, 8 → `Committed`) and the
tests go red. Verified: `cargo test -p dregg-tests --lib sovereign_witness_threats` → **21 passed, 0
failed, 3 ignored**.

### 4. FIXED — the preflight gate named `peer_exchange` exercised no peer exchange

`preflight/src/checks/sovereign.rs:106 check_sovereign_peer_exchange` — registered as
`run_check("peer_exchange", ...)` — never constructed a `PeerExchange`, never built a
`PeerStateTransition`, never called `verify_transition`, never verified a signature. It was `Ledger`
CRUD: register → get → `update_sovereign_commitment` → get. It calls the store **directly**, bypassing
every guard the protocol has. A comment saying "simulates peer exchange after state transition" was
doing all the work. **That gate would report GREEN with every peer_exchange guard deleted** — including
the fail-open in §1, which it sat next to the whole time.

This is the §-frame pattern exactly (`soundness` certifying a mock; the promotion gate proving
synthetic chains): a gate named for a security protocol, certifying that a hash-map works.

Fixed by adding `check_peer_exchange_protocol` (`:164`): two real sessions, one accepted signed
transition, then four adversarial legs each asserting a *specific* rejection — unknown peer, replay
(commitment mismatch), **v1 proof fails closed** (the §1 guard, now gated in preflight), forged
signature — plus a final assert that no rejection mutated the receiver's view. The CRUD half is kept
and honestly labelled.

**Verification status of §4:** the leg uses only APIs I confirmed against source
(`PeerExchange::new`, `create_transition`, `verify_transition`, `PeerExchangeError::*`,
`CellId::derive_raw`) and its logic is reviewed above. A clean compile-run was BLOCKED during my
window by a concurrent `target/` teardown (another lane's `cargo clean`-equivalent racing my build:
disk hit 100% full, then `.rmeta` files vanished mid-compile — `rand_chacha`, `either`, `syn`).
`cargo test --bin dregg-preflight preflight_sovereign` was rebuilding the full prover dep tree from
scratch at handoff. **Supervisor / next lane: re-run that to confirm §4 green** — §1 and §3 are
independently verified below and do not depend on it.

Leg ordering is load-bearing and commented: `create_transition` bumps the sender's sequence on every
call, and `verify_transition` checks sig → commitment → sequence → timestamp → proof. Minting the
proof-bearing leg after another rejected leg gives it a gapped sequence, so it trips `SequenceGap`
and asserts a guard I did not mean to test. I hit this while writing it; the proof leg is minted
first and the forged-signature leg last (its check fires before sequence is read).

### NOT FIXED — named

- **Rule 8 has a LIVE producer on the operator surface, and it lies.** The MCP tool
  `sovereign_witness_sign` exposes `attach_proof` — advertised (`node/src/mcp/tools_def.rs:1048`) as
  *"If true, also generate a STARK transition_proof binding (old, new, effects_hash) via
  EffectVmAir."* Set it and `handlers_verify.rs:614-648` really does generate an EffectVmAir proof and
  put it in `transition_proof`. The executor then **rejects that turn outright** (rule 8). So a
  documented, advertised option mints a guaranteed-dead artifact — and the tool's own returned `note`
  (`handlers_verify.rs:666`) tells the operator *"the executor will re-verify the Ed25519 signature
  ... and (when present) the STARK transition_proof."* It will not; it will refuse. Nothing tests this
  path. This is why my rule-8 test matters: the guard is reachable from the operator surface, not
  hypothetical. Fix needs an owner call (retire `attach_proof`, or make it error at the tool boundary)
  and `node` does not currently build here (see in-flux note).
- **Stale docs asserting a capability the code rejects.** `turn/src/turn.rs:92-94` still says "If
  `transition_proof` is `Some`, the STARK is verified via `EffectVmAir`…", and `:123-125` says the
  executor "may verify in lieu of re-executing." Both describe the retired v1 path that
  `execute.rs:940` refuses. Left alone (doc-only, and `turn/` is hot with other lanes) but they should
  go — they are how someone talks themselves into re-opening the gate.
- **`PeerStateTransition::unilateral_attestation` is inert.** `verify_transition` **never reads it**
  (`peer_exchange.rs:82` is a field decl; the only other mentions are three `: None` constructions).
  Its own 20-line doc (`:63-83`) claims the receiver "re-derives the canonical attestation_data from
  the sender's cell-id-derived encoding and confirms the bundle's `UNILATERAL_ATTESTATIONS_*` PI
  accumulator absorbed exactly this attestation — closing the executor-trust gap on sovereign-cell
  self-witnessing." `verifier/src/bilateral_pair.rs:66` repeats the claim from the other side. **No
  code does any of this**, and like `transition_proof` the field is outside the signature. An
  executor-trust gap documented as CLOSED is open. Implementing γ.2 unilateral binding is a feature,
  not a test fix — it needs an owner.
- **`ReqwestTransport` / the 11 real phantom cfg sites / `unexpected_cfgs = "allow"`** — §2.
- **`wasm` is excluded from the workspace** (`Cargo.toml:68`), so `cargo check --workspace` never
  builds it. `wasm/src/runtime.rs:2869` matches on `PeerExchangeError` — a variant rename would not
  go red in any workspace build. Same silent-gate family as the missing CI remote.
- **3 `#[ignore]`d AIR-teeth tests** (`sovereign_witness_threats.rs:443,541,799`) — all blocked on
  sovereign-witness AIR teeth (T9). Honestly labelled, not vacuous, but they are the tests that would
  bind the witness to the *transition* rather than the receipt. Still owed.
- **Observation, not a defect:** a turn rejected in the sovereign-witness pre-pass still bumps the
  agent's nonce (`NonceReplay { expected: 1, got: 0 }` on a re-submit). Defensible as anti-DoS
  charging; noting it because it surprised me and forced my rule-8 control leg onto a fresh fixture.
- **In-flux, not mine:** `dregg-lean-ffi/build.rs:1605` fails to compile (arity: 5 args to a 6-arg
  `build_dregg2_archive`), which blocks `cargo check -p dregg-node`. It is modified in the working
  tree — another lane mid-edit. Also note `target/` was being torn down concurrently during this lane
  (disk hit 100% full, `.rmeta` files vanishing mid-build); builds here may need retries.

## 2026-07-16 — Lane 1: taxonomy + power census — the estate is strong at the core; the rot is SILENCE mechanics, not missing teeth

### The census (whole workspace, ~184 crates)
- **~14,981 test fns** (14,631 `#[test]` + 350 `#[tokio::test]`) across **179 crates**; 750 integration-test files in `tests/` dirs; 335 `#[ignore]` attribute lines; 12 `benches/` dirs.
- **By family**: unit tests everywhere; integration heavy in circuit(-prove), turn, sdk, node, teasting; **property-based** concentrated in protocol-tests (~65 proptest sites), redteam (~25), pg-dregg, turn, cell, tests — near-zero elsewhere; **differential** is a real institution (exec-lean's 9-suite Rust<->Lean estate incl. `rejection_parity.rs` (979 lines) + `rust_lean_parity_gauntlet.rs` with explicit non-vacuity floors (>=5 BOTH-REJECT / byte-identical BOTH-ACCEPT); `dregg-dsl-differential` drives 7 backends to an agreement matrix; `dregg-lean-ffi/tests/direct_vs_json_differential.rs` pins the no-copy FFI against the JSON oracle); **e2e** = teasting (42-file multi-node sim: byzantine/crash/ordering faults, cross-federation) + node real-process kill sims (`consensus_under_failure.rs`); **adversarial** = redteam (13 attack files incl. proptest-driven `wire_codec_fuzz.rs`/`marshal_fuzz.rs`), tests/src (soundness, executor_honesty_threats, sovereign_witness_threats), lightclient rejection batteries; **coverage-guided fuzz**: only `orb/conformance/fuzz` — nothing chews on the kernel wire, captp, or persist.
- **Rejection-vs-acceptance balance in the security crates is healthy by name AND spot-check**: verifier 40/57 rejection-shaped test names, eth-lightclient 111/157, captp 97/281, cell-crypto 62/171. `persist/src/commit_log.rs` really tests torn-tail truncation, crash-mid-write recovery, and fail-closed genuine corruption (`recover_from_base_fails_closed_on_genuine_corruption`, commit_log.rs:2411). App-tier game crates are shallow but still carry refusal tests (dreggnet-quest/src/lib.rs:572 `out_of_order_step_is_refused_then_commits`).
- **`#[ignore]` hygiene is good**: nearly all 335 documented (SLOW recursion folds routed to the nextest `armed` lane, GPU lane, live-device, generator one-shots). The 22 in `tests/` are honest "blocked on X" tracker refs — ~22 KNOWN-MISSING adversarial AIR teeth (sovereign-witness AIR binding, gamma.2 composition, caveat rows): named debt, not hidden breakage.
- **Frame update**: the "this clone has NO GitHub remote" root cause is GONE as of today — `origin` = github.com:emberian/dregg, `origin/main` has a commit from 2026-07-16 16:33 ("ci: stop interpolating federation node identity keys"). ci.yml / armed-teeth.yml can now actually bind. VERIFY the armed-teeth schedule really fires (GitHub auto-disables scheduled workflows on 60-day-quiet repos).
- My assertion-free-test scan flagged 197 candidates; every one I read (~40) was a false positive (delegating to asserting helpers) EXCEPT the sidetable husk below. Scan = ~30-line python walker (test-attr -> fn body brace-scan -> no assert/panic/unwrap/is_err); worth re-running post-swarm.

### Top weaknesses (importance x weakness) and what I did
1. **[FIXED + VERIFIED] The entire Rust<->Lean differential estate self-skipped SILENTLY.** `dregg-lean-ffi` ships a purpose-built fail-loud gate — `demand_lean` (dregg-lean-ffi/src/lib.rs:135; unarmed: honest skip; `DREGG_TEST_REQUIRE_LEAN=1`: panic) — whose own docstring names this exact hole... but it was only ever wired into `node/`. All 9 exec-lean differential suites, `sdk/tests/lean_producer_surface.rs`, and `dregg-lean-ffi/tests/direct_vs_json_differential.rs` used raw `if !lean_available() { return; }` — on an archive-less build THE-SWAP differentials, rejection parity, and the parity gauntlet all report `ok` having asserted NOTHING, even on the hard-mode lane. Converted all 17 sites in 13 files to route through `demand_lean` (exec-lean/tests/{lean_state_producer_{widen,coverage,sidetable,denotational_census,differential},faucet_fee_well_divergence,committed_height_effect_families,speculative_audit,fulfillment_ffi_verified,rust_lean_parity_gauntlet,rejection_parity}.rs; sdk/tests/lean_producer_surface.rs; dregg-lean-ffi/tests/direct_vs_json_differential.rs) + refreshed the now-stale docstrings. VERIFIED: all 13 targets compiled and RAN green under `DREGG_TEST_REQUIRE_LEAN=1` with the archive linked (67 tests executed, not skipped). The armed-missing->PANIC pole is pinned end-to-end by dregg-lean-ffi's own `demand_lean_armed` unit tests (lib.rs:190, catch_unwind). I did NOT fault-inject `lean_available()` in production src for a live end-to-end red — two other lanes were building/running against dregg-lean-ffi in this shared tree all session.
2. **[FIXED — runtime verification PENDING, see below] `exec-lean/tests/lean_state_producer_sidetable.rs` was a ZERO-TEST HUSK.** 173 lines: a docstring claiming "the Rust executor's commit ... is still asserted", full helper set, and NO `#[test]` AT ALL — a test target reporting `ok. 0 passed` forever (caught because a 0-test binary surfaced in my armed sweep; committed that way at HEAD). Worse: `rust_lean_divergence_finder.rs:294,764` cite its replacement tooth — `lean_state_producer_coverage::queue_falls_back_factory_dissolved` — which was NEVER WRITTEN anywhere (phantom citation): the dissolved-verb wire-refusal property had NO test in the repo. And it is a REAL adversarial surface: the kernel no longer parses `cesc`/`cobl` (F1b factory-dissolution), so stale/malicious PEER BYTES carrying one must refuse loudly, never be silently skipped-and-committed (parse-confusion -> unauthorized state install). Rewrote the file as that tooth: take a conformance-corpus wire that COMMITS at baseline, swap its `{"bal":[...]}` action tag for `cesc`/`cobl`/`zzzz`, assert the verified kernel refuses; plus `baseline_bal_wire_commits` as the non-vacuity floor (if the baseline stops committing, the refusal teeth are exposed as vacuous and it goes red).
   **HONEST STATUS**: the rewrite could NOT be compiled+run in-session — the disk hit 100% (ENOSPC) and tore `target/` artifacts mid-run (ark-std/num-traits/num-bigint/darling_core; fixed by targeted `cargo clean -p`, never a full clean), and the rebuild then queued for hours behind (a) a sovereign-prove lane holding the main build lock and (b) a full `lake` rebuild of the Lean archive that build.rs triggered (the Lean tree changed today). The run is QUEUED and will land: `cargo test -p dregg-exec-lean --test lean_state_producer_sidetable`. Its API usage mirrors `direct_vs_json_differential.rs` verbatim (same 4 public fns, signatures read from source). Bite-proof once it runs: (i) `baseline_bal_wire_commits` green proves non-vacuity; (ii) disable the mutation (`mutant = wire.clone()`) -> the SILENT-STATE-INSTALL assert MUST go red on the committing baseline; re-enable -> green. If `dissolved_*_refuses_loudly` goes RED on the real kernel, that is not a broken test — it is a genuine parse-confusion FINDING (silent skip-and-commit of unknown verbs) and must be treated as such.
3. **[NOT FIXED] Coverage-guided fuzzing is absent at the trust boundaries.** redteam's proptest fuzzes are real but structure-aware; nothing coverage-guided ever runs against `dregg_wire::codec`, the postcard `Turn` surface, the hand-rolled FFI wire grammar (`dregg-lean-ffi/src/marshal.rs` — hand-written encoder, kernel-side recursive parser; EXACTLY the shape cargo-fuzz eats), or persist's redb images. Deferred proposal: a `fuzz/` workspace member, 3 targets, seeded from `conformance_input_corpus()`.
4. **[NOT FIXED] The armed lane depends on someone running it.** The minute-scale teeth (135 `#[ignore]`s in circuit-prove: recursion folds, binding mechanisms, VK determinism) only execute via `scripts/test-gauntlet.sh armed` / armed-teeth.yml's schedule. With the remote newly live this may now be real — but confirm the schedule fires.
5. **[NOT FIXED] The 22 "blocked on" ignored teeth in `tests/`** (sovereign-witness AIR binding, gamma.2, caveat-correctness rows) are the largest coherent block of known-missing adversarial coverage; they need their BLOCKERS scheduled, not test-side work.

### Family power map (for the next lane)
- REAL TEETH: exec-lean differential estate; redteam attack suites; persist crash-consistency; eth/cosmos-lightclient rejection batteries; teasting fault sims; circuit-prove emit-gates; the parity gauntlet's non-vacuity floors.
- THIN / SHAPE-ONLY (by importance): FFI wire grammar fuzz (none) > armed-lane execution guarantee > sovereign-witness AIR block (known-blocked) > app-tier dreggnet-* depth > deos-* UI crates.

### In-flux (not defects, other lanes' work)
Shared tree was HOT all session: a sovereign-prove lane held the main build lock for ~3h; a `lake` full-archive rebuild ran across 4 target dirs; disk hit 100% ENOSPC and tore target/ artifacts (recovered via targeted `cargo clean -p`); `Cargo.lock`, `circuit*/`, `preflight/`, `deploy/` dirty states belong to other lanes and were not touched. My queued sidetable verification run may complete after this entry — harvest its result rather than re-running blind.

## 2026-07-16 — mocks-mirrors-fakes/sdk-bridge — credentials::present()+verify() default round trip did ZERO crypto verification (and a self-asserting "tamper" theater test)

Slice: `credentials/` (the promoted `dregg-credentials`, re-exported as the production surface by `starbridge-apps/identity`). Two scout candidates, both CONFIRMED from code; one more mock found while verifying them.

**Both candidates VERIFIED (not refuted):**

1. **MOCK — `present()` shipped the unsound path as its default** (`presentation.rs:295-308`). The module doc promised "Full STARK ... suitable for cross-trust-boundary verification"; the code called `BridgePresentationBuilder::prove_local_constraint_check_only()` via `UnsafeLocalOnlyMarker::i_know_this_is_not_cryptographically_sound()` for EVERY non-anonymous presentation — the bridge documents that path (`bridge/src/present.rs:815-828`) as "NOT CRYPTOGRAPHICALLY SOUND ... Do NOT use for untrusted provers or cross-trust-boundary verification". A stale comment promised a `prove_real = true` option that never existed on `PresentationOptions`.

2. **FAKE — `verify()` waved LocalOnly through by default** (`verification.rs:157-165`). The LocalOnly acceptance was gated on `options.require_anonymous`, which is `false` by `Default`. Since `present()` also only ever produced LocalOnly, the crate's DEFAULT `present()`+`verify()` round trip performed zero cryptographic verification and still returned a `VerifiedPresentation`. Anyone holding the credential bytes could mint a "proof" the verifier accepts — the `verified: bool` sin this crate's own doc criticizes `apps/identity` for. Cross-checked against the codebase's own stricter `verify_proof_complete` (`present.rs:2271`, unconditionally requires `real_stark_proof`), confirming `verify()` was a strictly-weaker shadow contract.

**Fix (REWIRE to the real counterpart, ember's preferred fix):**
- `present()` and `present_anonymous()` now both call the real STARK `prove()`. Measured: the ~30s cost the mock was justified by is stale — full `present()`+`verify()` over the 4-attr fixture runs in <1s (debug). The dev-only LocalOnly path survives ONLY behind a new, explicitly-named `present_local_only_unsafe(.., &UnsafeLocalOnlyMarker)`, whose output `verify()` refuses.
- `verify()` now rejects LocalOnly **unconditionally** (`LocalOnlyRejected`), and requires `proof.is_valid()` (real STARK present) regardless of any anonymity flag — the mint-a-consistent-fake path is closed for the default verifier, not just the anonymous one.

**Third mock found while verifying (THEATER + a missing check):** `integration_present_verify_full.rs::tampered_disclosed_value_is_caught_by_verifier` asserted NOTHING — it ran `verify()` on a tampered disclosure and then `if let Ok(vp) = result { assert_eq!(vp.disclosed[0].1, tampered_value) }`, i.e. if the verifier ACCEPTED the tamper it checked the accepted value was the attacker's, and PASSED. Twenty lines of "either outcome is documented" prose over a hole: `verify_inner` had NO revealed-facts-commitment check at all, though the module doc lists it as rejection reason 4 and `present.rs:250` binds `revealed_facts_commitment` into the STARK public inputs (`present.rs:315` doc: "The verifier recomputes from the plaintext facts and checks equality" — it never did). This could not have worked pre-rewire (LocalOnly binds nothing); now that `present()` emits a real STARK it has teeth. Added the check (`RevealedFactsMismatch`), reusing the prover's `compute_revealed_terms_commitment` (`pub(crate)`, one function both sides — no shadow), covering both the swap and the strip-to-empty downgrade.

**Teeth PROVEN to bite:** reverted `verify()` to the old `require_anonymous`-gated behavior → `local_only_proof_rejected_by_default_verify` FAILED with "SOUNDNESS: default verify() ACCEPTED a non-cryptographic LocalOnly proof" at 0.02s; restored the fix → green. Note the pre-existing `local_only_proof_rejected_by_verify_anonymous` never bit its own name (fed a non-anonymous proof to `verify_anonymous`, so `AnonymityMismatch` fired first and the test accepted either error) — the new `_by_default_verify` test targets the actual default hole.

**Verification:** `cargo test -p dregg-credentials` → 33 passed, 0 failed across anonymity_soundness (10), attenuation_soundness_differential (6), integration_present_verify_full (10), roundtrip (7). Includes `present_produces_a_real_stark_proof` (asserts `real_stark_proof.is_some()` + `is_valid()`), rewritten tamper test, and new `stripped_disclosure_is_caught_by_verifier`.

**SKIPPED as dirty (reported, not touched):** `credentials/src/presentation.rs` carried one uncommitted hunk from the blinded-value/fact-weld lane (the `fresh_predicate_blinding()` predicate-blinding edit at :346-358, quiescent ~1h). My edits are in disjoint regions (prover selection, doc, commitment helper visibility) and coexist cleanly — the file built and the full suite passed with both sets of changes present. Its pre-existing `use dregg_circuit::poseidon2;` unused-import warning is that lane's, left untouched.

**Environment:** shared-tree disk hit 100% ENOSPC mid-session (another lane's bare `cargo clean` on the workspace tore `target/debug/deps`); recovered; 25-way cargo-test lock contention serialized the rebuild. All results above are post-recovery, clean-tree.

**Committed NOTHING** — supervisor gates.

## 2026-07-16 — Lane 6 (verification↔validation gap + rot) — the emit gates were certifying bytes Lean stopped emitting

### (a) THE GAP — the "equality gate" never compared its two sides

Every `circuit-prove/tests/*_emit_gate.rs` embeds a `GOLDEN_JSON` documented as byte-identical to a
Lean `#guard` pin ("a drift on either side breaks THIS `#guard` (Lean) or the Rust `assert_eq!` —
neither can silently diverge", `metatheory/Dregg2/Circuit/Emit/FoldEmit.lean:234-236`). That claim was
structurally unenforceable: the Lean `#guard` checks Lean-emit vs Lean-literal at `lake build`; the
Rust test checks Rust-literal vs Rust-hand-built at `cargo test`. NOTHING executable compared the Lean
literal to the Rust literal — each side welds only to itself, so the PAIR drifts while both gates stay
green. A gate comparing two checked-in copies of one claim validates nothing about their agreement.

**Found (mechanically): 6 drifted goldens across 5 descriptors, committed** — in the tree since the
2026-07-15 fresh-cut genesis `ddd2408c5`; the pairs have NEVER matched in this repo's history:

- `dregg-fold-step-v2` — 17 vs 20 constraints (`fold_emit_gate.rs` + `fold_emit_audit_extra.rs` vs
  `FoldEmit.lean`) — **FIXED, see below**
- `dregg-derivation-v1` — 379 vs 393 (`derivation_emit_gate.rs` + `derivation_emit_audit_extra.rs`);
  delta = 14 pi_bindings + PI count 6→13: Lean binds SEVEN claim slots the Rust-certified version
  leaves unexposed
- `dregg-garbled-evaluation-extended-dsl-v1` — 32 vs 47 (`garbled_eval_emit_gate.rs` +
  `garbled_eval_audit_extra.rs`); delta = 15 boundary constraints (1→16): fifteen pins the
  Rust-certified version does not enforce
- `dregg-non-revocation-sorted-tree::poseidon2-v1` — 14 vs 20 (`non_revocation_audit_boundary.rs` vs
  `NonRevocationEmit.lean`)
- `dregg-predicate-arith-ge::threshold-v1` — 5 vs 7 (`predicates_arithmetic_boundary_audit.rs`;
  drift confirmed against the COMMITTED `PredicatesArithmeticEmit.lean`, not the in-flux copy)
- `dregg-relational-predicate-ir2-v1` — 91 vs 219 (`predicates_rc_audit_extra.rs` vs
  `PredicatesRelationalCompoundEmit.lean`)

**The fold drift is a PROVEN soundness drift.** The 17-constraint descriptor the gate certified (with
a full passing canary suite) admits removal-count inflation: nothing pins the count chain's origin
(row-0 `REMOVAL_COUNT` free) and nothing defines the `REMOVAL_COUNT_PLUS_ONE` aux column, so a prover
shifts every count coordinate consistently and publishes any total. **Executed proof**: a scratch test
built that witness (2 removal rows, claimed `pi[2] = 7`) against the retired golden — it PROVED and
VERIFIED end-to-end through `prove_vm_descriptor2`/`verify_vm_descriptor2` (run once, then deleted).
Lean had already fixed the hole (`first_removal_count` RC=0 boundary + `removal_count_plus_one`
definition gate + `removal_count_carry` window, `FoldEmit.lean:150-208`); the Rust gate kept
certifying the broken bytes, green, for the repo's whole life.

**FIXED:**
1. `scripts/check-emit-gate-weld.py` — the cross-language weld gate (static, <1s, no lake/cargo):
   extracts every descriptor golden from `circuit-prove/tests/*.rs` (ALL tests — the `*_audit_*`
   family embeds the same goldens and rots identically), requires byte-equality with a Lean `#guard`
   pin or a `circuit/descriptors/**` artifact (JSON + staged TSV registries — those inherit the
   generate-fresh gate `scripts/check-descriptor-drift.sh`). Exit 1 on a drifted pair or an unwelded
   golden; also prints the reverse gap. **Proof it bites: it is RED right now** on the five unfixed
   descriptors above. Wired into ci.yml's `descriptor-drift` job as a step after the drift gate.
2. `circuit-prove/tests/fold_emit_gate.rs` — re-welded to the CURRENT 20-constraint Lean descriptor:
   fresh `GOLDEN_JSON`, hand-built twin extended with the three new constraints, honest trace moved to
   RC-counts-removals-BEFORE-this-row semantics (kills the old `is_last_removal` hack), and a NEW
   canary `inflated_removal_count_refuses` pinning the exact attack the retired descriptor admitted
   (asserts honest-accepted first — non-vacuous). Verified: `cargo test -p dregg-circuit-prove --test
   fold_emit_gate` → 10/10 pass.
3. `circuit-prove/tests/fold_emit_audit_extra.rs` — same re-weld (found only after widening the weld
   gate's glob beyond `*_emit_gate.rs` — the lesson is in the gate now). Verified: 2/2 pass.

**NOT FIXED (named):** the four remaining drifted descriptors above need the same re-weld surgery
(golden + hand-built twin + witness rework, up to 393-constraint scale) — too large to do blind in
this lane; `check-emit-gate-weld.py` stays RED until then and that red is honest — do not baseline it
away. Also named: `dfa-routing-injection-3state::poseidon2-v1` (`DfaRoutingGeneralEmit.lean`) is
`#guard`-pinned in Lean with NO Rust-side counterpart at all (no golden, no artifact — Lean-only,
zero artifact validation).

**Coverage map for question 5** (verification with no validation): 35 Rust goldens / 49 Lean `#guard`
pins / 287 checked-in descriptor artifacts. The `circuit/descriptors/**` surface is honestly gated
(check-descriptor-drift.sh re-derives from fresh oleans — a true generate-fresh gate, not a
two-stale-copies compare). The in-test golden surface was the unguarded seam; it now has a gate that
can go red.

### (b) THE ROT — an entire crate's examples never compiled, and each failure hid the next

`cargo check --workspace --all-targets` (exactly the ci.yml gate that never runs on this remote-less
clone) failed on arrival at `demo-agent/examples/note_privacy.rs` (5 errors) — and because cargo
aborts the crate on first failure, the rot behind it surfaced only as each layer was fixed. Full
census of demo-agent example rot, all silent-not-red:

- **~26 call sites** of single-arg `NullifierSet::insert` across TEN files — the signature grew a
  `value: u64` (`cell/src/nullifier_set.rs:137`) and zero example call sites were updated:
  `note_privacy`, `private_orderbook`, `cdt_revocation`, `nft_demo`, `auction_demo`,
  `atomic_swap_demo`, `private_auction`, `base_private_transfer`, `note_bridge`, `token_revocation`,
  `unified_harness`. ALL FIXED (spent note's `.value()`; revocation markers record 0).
- **Retired STARK APIs** from the stark-kill wire flip still imported/called:
  `prove_note_spend`/`verify_note_spend` (note_privacy, base_private_transfer),
  `verify_issuer_stark` (unified_harness, multi_org_delegation, sub_agent_spawn, and
  `tests/src/full_pipeline.rs` — a TEST crate certifying via a method that no longer exists),
  `issuer_proof_bytes` (multi_org_delegation). ALL FIXED: note-spend flows rewritten onto the
  DEPLOYED IR-v2 leaf path (`descriptor_by_name(NOTE_SPEND_LEAF_NAME)` + `note_spend_witness` +
  `prove_vm_descriptor2`, verifier rebuilding the 7-slot claim from public data exactly as
  `turn/src/executor/apply.rs::verify_note_spend_descriptor2`); issuer-stark asserts replaced with
  the preflight-blessed pattern — `has_real_stark_proof()` + `verify_presentation_bb` + the
  WRONG-ROOT refusal tooth (each site now proves the root binding bites, which the old assert never
  did).
- Verified: `cargo check -p dregg-demo-agent --bins --tests --example <12 fixed examples>` → green;
  `cargo check -p dregg-tests --all-targets` → green.

**NOT FIXED (named, blocked):** `private_auction.rs` + `private_hiring.rs` import the retired
predicate convenience APIs (`prove_predicate`/`verify_predicate`, `prove_committed_threshold`/
`verify_committed_threshold`, `prove_compound_predicate`/`verify_compound_predicate`) whose
replacement surface (`circuit/src/predicate_*_witness.rs`, `dsl/predicates/*`) is DIRTY — actively
being rewritten by another lane this session. Rewriting against a moving surface would collide;
these two stay red in `--all-targets` until that lane lands. Whoever picks them up: the migration
shape is the same descriptor-dispatch pattern as note-spend.

**NOT rot (checked, honest):** every `#[ignore]` in the tree is labeled slow/live-hardware with a
run-with-`--ignored` note; `required-features`-gated targets are deliberate and documented
(deos-hermes zk-live, pg-dregg pgrx, dregg-lean-ffi lean-lib, bridge test-utils); no orphan test
files (every `tests/` subdirectory module is referenced via `mod`/`#[path]` — checked
dreggnet-game-board, sdk, cosmos-lightclient, circuit-prove, eth-lightclient).

**Environment (corroborating the entry above):** hit the same 100%-full data volume mid-lane (ENOSPC
killed builds mid-rmeta-write); freed `target/debug/incremental`, adopted a private
`CARGO_TARGET_DIR` after losing ~1h to the shared `target/debug` build-dir lock queue behind
long-running lanes. Recommend the private-target-dir pattern for all verification lanes while the
swarm is hot.

**Committed NOTHING** — supervisor gates.

## 2026-07-16 — mocks-mirrors-fakes/turn-cell — FoldDelta.verify was self-consistent theater; now recomputes the root + rejects capabilities-as-checks

**CONFIRMED + FIXED** the scout's HIGH candidate. `commit/src/fold.rs::FoldDelta::verify`
(doc: "the new root matches expectation") did NOT recompute `new_root`. Its only root checks
compared `surviving_proof.old_root/new_root` against `self.old_root/new_root` — two fields on
the SAME author-supplied struct. `added_checks` were accepted on `!predicate.is_zero()` alone
(line 130), never a rule-prefix check. The declared `FoldVerification::RootMismatch` variant was
NEVER constructed (grep-confirmed dead). A delta could name a `new_root` belonging to a WIDER
state (more capabilities) and `verify` returned `Valid`. Two widening paths existed:
  (i) a `new_root` the author simply invented — refuted only by recomputation;
  (ii) a raw capability fact smuggled in as an "added check" (root-consistent) — refuted only by
       a rule-prefix policy.

Production reach CONFIRMED: `bridge/src/present.rs::TokenPresentationChain::verify_chain` (the
gate feeding "Generate a real STARK-backed presentation proof") called `delta.apply_and_verify()`
— the weak path — while the sound `reconstruct_new_state(&old_state)` was already used correctly
in `bridge/src/delta.rs`.

FIX (rewire to the sound counterpart, per pref #1):
- `FoldDelta::verify(&self, old_state, policy)` / `apply_and_verify(&self, old_state, policy)`:
  now (a) binds `old_root == old_state.root_immutable()` (new `OldRootMismatch`), and (b)
  RECOMPUTES the post-state via `reconstruct_new_state(old_state)` — returns `RootMismatch` unless
  it yields `new_root`. Load-bearing tooth. Removed the self-admitting
  `reconstruct_new_state_for_verify` ("we cannot independently recompute new_root") — its
  structural checks fold into `verify`.
- New `CheckPolicy` (`NoAddedChecks` fail-closed | `RuleNames(&[&str])`): an added check is
  admitted only if its predicate hash equals `from_symbol("rule:<name>")` (or `..._<index>`) for
  an allowlisted name. Not rule-prefixed => `InvalidCheck`. Forging a non-rule fact past this
  needs a BLAKE3 preimage collision.
- `verify_fold_chain(genesis, deltas, policy)`: walks forward from the verifier's own genesis
  state, reconstructing each intermediate root; continuity is no longer taken on the deltas' word.
- Production: `present.rs::verify_chain` now verifies each delta against the REAL prior
  `chain[i-1].state` with `CheckPolicy::RuleNames(VALID_CHECK_PREDICATES)` (the same allowlist the
  build side enforces) and binds each `new_root` to the step's actual state.

TEETH PROVEN TO BITE (mutation test): reverted both teeth in `fold.rs` and re-ran —
`forged_widening_delta_is_refused`, `capability_smuggled_as_added_check_is_refused`,
`rule_outside_the_allowlist_is_refused`, `no_added_checks_policy_is_fail_closed` all FAILED with
`left: Valid` (the old code's answer to a forged widening delta). Restored => 131/131 green.

ALSO fixed adjacent THEATER in `tests/src/commitment.rs::fold_delta_adding_capability_without_check`:
it set `removed:[]` + `added_checks:[]`, tripping the `EmptyDelta` guard BEFORE any root check, and
asserted `EmptyDelta` — the fake `new_root` was never exercised, so it proved nothing about
widening. Rewrote into three real cases (forged root => `RootMismatch`; capability-as-check =>
`InvalidCheck`; empty => `EmptyDelta`, noted as a separate guard). Added
`fold_delta_with_consistently_tampered_new_root` (tampers BOTH root copies so the delta is
self-consistent — the real forgery the old tamper tests missed).

Callers threaded through (all were clean; verified via `cargo check` in a private
`CARGO_TARGET_DIR`): `dregg-commit` lib tests (131 pass), `dregg-bridge` (lib+tests type-check
clean), `dregg-tests` (commitment.rs+fuzz.rs), `dregg-demo-agent` (ivc_attenuation_chain +
unified_harness examples), `dregg-wasm` (full check; removal-only demo => `NoAddedChecks`).

NAMED (not fixed — out of this slice, no live reach): `commit/src/state.rs:162
is_rule_field_element` returns `false` unconditionally (a stub — "For production use, the symbol
table should be consulted"). Its only callers are `TokenState::facts_only`/`rules_only`, which have
ZERO callers repo-wide (grep-confirmed) — dead, so no live break today. The correct home for a
real rule-tag test is the symbol table; my `CheckPolicy` re-derives the `rule:` predicate hash
instead of relying on this stub, so the verifier path no longer depends on it. Left in place for a
retire-the-dead-code lane.

Could NOT link the `dregg-bridge` runtime test binary: pre-existing ENVIRONMENT issue — the
`libdregg_lean.a` archive is incomplete (undefined `_initialize_Dregg2_Metatheory_*` /
`_initialize_mathlib_*`; its own build script warns it "lacks dregg_exec_handler_turn"). Blocks any
test binary linking the Lean FFI, independent of these changes; `cargo check --tests` (no final
link) is clean.

**Committed NOTHING** — supervisor gates.

## 2026-07-16 — assumption-ledger swarm (supervisor harvest) — inventory done, rig phase LOCK-BLOCKED
The 4-domain assumption swarm (wf_e644d5d0-de4) INVENTORIED real un-rigged assumptions but its OPUS RIG
lanes are BLOCKED waiting on the build lock (a ~56-min Lean build another lane holds) — so no mutation-tested
rigs landed yet; the workflow is still live and will resume when the lock frees. Supervisor triage of the
inventory:
1. `peer_exchange.rs:287` non-strict ed25519 on peer transitions — **STALE finding: already `verify_strict`**
   (fixed during the swarm, with an explicit "peer_pubkey is caller-supplied off the wire" comment). No action.
2. The ~26 EffectVM descriptor `_FP` sha256 pins are IGNORED by `all_descriptors_parse` (binds `_fp` with `_`)
   — but this is NOT theater: the file's own comment (:10) correctly notes a rehash is self-referential, and
   the REAL generate-fresh drift gate `scripts/check-descriptor-drift.sh` (re-emit from Lean + diff) IS wired
   into CI (`.github/workflows/ci.yml:497`). So the assumption "descriptors match the Lean emission" IS
   rigged — contingent only on the standing "does CI actually run on the new remote" ember-decision.
3. `BridgePresentationBuilder::add_attenuation` (bridge/present.rs:670) MAX_FOLD_DEPTH bound — the sole
   remaining enforcer, UN-RIGGED (no test trips it). REAL gap. Rig: a test that a chain exceeding
   MAX_FOLD_DEPTH is refused. (bridge/present.rs is dirty from another lane — rig on a settled tree.)
4. `EpochMinter::maybe_mint` (turn/economics.rs:205) — treasury-absent-at-epoch-boundary returns None WITHOUT
   advancing last_minted_epoch → potential re-mint next epoch. Worth a rig confirming the epoch DOES advance
   (or that the skip is intended). REAL gap.
NEXT: let the swarm's rig lanes finish when the lock frees; rig #3/#4 (the two real gaps) either via the
swarm or by hand on a settled tree.

## 2026-07-17 — board/Lane D — the 629(->1217 measured) dangling `docs/*.md` citations: 1059 mechanically repointed, 80 named unresolved

**Scope check first.** `git grep -nE 'docs/[A-Za-z0-9_./-]+\.md' -- . ':!.docs-history-noclaude'` over
tracked files (9971 files; the 233G working copy is too big to `grep -r`, use `git grep`) found **2859**
boundary-checked `docs/*.md` mentions. Resolving each against the CITING FILE's own ancestor chain (a ref
inside `metatheory/docs/X.md` or `pg-dregg/docs/X.md` legitimately means the sibling file, not
repo-root `docs/`) — the brief's "629" underestimated it: **1217 lines cited a `docs/*.md` path that does
not exist anywhere reachable from the citing file, across 197 distinct targets.**

**Method (mechanical, not manual-per-line) — verified safe before applying at scale:**
1. Built an index of every real `.md` file under `docs/`, `metatheory/docs/`, `pg-dregg/docs/`, and
   `.docs-history-noclaude/` (`os.walk`, existence-checked).
2. Classified each of the 197 dangling targets: **34 MOVED** (renamed/relocated — found live under
   `docs/design-frontiers/`, `docs/SUPERSEDED/`, `metatheory/docs/`, or `pg-dregg/docs/` by basename,
   single unmabiguous match each — checked, zero ambiguous multi-matches); **124 ARCHIVED** (found in
   `.docs-history-noclaude/`, again unambiguous); **39 GONE** (not found anywhere — genuinely never
   written, or truly deleted with no archive copy).
3. Confirmed the repo's OWN convention for archived pointers before choosing mine:
   `HORIZONLOG.md:1441` already writes `` `.docs-history-noclaude/EMBEDDABLE-LEAN-RUNTIME.md` `` directly
   — direct-repoint, no extra "(archived)" annotation needed, matches `HORIZONLOG.md:7521`'s own note
   about the same class of dead link. Used the same pattern.
4. **`git status --short` FIRST**: 255 pre-existing dirty files. Any citing file already dirty was
   **skipped entirely** (17 files, 30 dangling lines) — reported below, not touched.
5. Applied a boundary-safe substring replace (`(?<![A-Za-z0-9_./-])docs/X\.md` → resolved path) per
   **clean** citing file, operating on real file reads (not on any grep-truncated text) so an
   already-correctly-prefixed occurrence (e.g. a line that already said
   `metatheory/docs/CELL-PROGRAM-LANGUAGE.md`) could never be double-prefixed. **Verified this held**:
   `grep -rn "metatheory/metatheory/docs\|pg-dregg/pg-dregg/docs\|docs-history-noclaude/\.docs-history-noclaude"`
   over the whole tree post-edit → **zero hits**.

**Result — 1059 citations fixed across 416 files, zero collisions with other lanes' dirty files (checked
by set-intersection, not by eye):**
- **(a) 117 lines — MOVED, repointed to the real live path.** E.g. `docs/AGENT-SWARM-UX.md` →
  `docs/design-frontiers/AGENT-SWARM-UX.md`; `docs/CELL-PROGRAM-LANGUAGE.md` → the sibling
  `metatheory/docs/CELL-PROGRAM-LANGUAGE.md` (36 sites incl. `cell/src/blueprint.rs:95,106`,
  `cell/src/predicate.rs:675`, `cell/src/state.rs`); `docs/QUICKSTART-pg-user.md` →
  `pg-dregg/docs/QUICKSTART-pg-user.md`; `docs/NULLIFIER-ACCUMULATOR-*.md` →
  `docs/SUPERSEDED/NULLIFIER-ACCUMULATOR-*.md`.
- **(b) 942 lines — GENUINELY ARCHIVED, repointed to `.docs-history-noclaude/`.** This is the
  brief's top offender and it checks out: **`docs/PG-DREGG.md` had 137 dangling citing lines** (not 89 —
  the brief's count was itself stale/an undercount), now all `` `.docs-history-noclaude/PG-DREGG.md` ``.
  Fixed the exact instance the brief called out: `pg-dregg/Cargo.toml`'s `[workspace]`-exclusion
  justification (lines 5, 10, 75, 103 — four separate `docs/PG-DREGG.md` citations in that one file, not
  one) plus `docs/PG-DREGG-PG18.md`, `docs/EMBEDDABLE-LEAN-RUNTIME.md`, `docs/PG-DREGG-VS-DBOS.md` in the
  same file. Also `node/Cargo.toml:99`, `pg-dregg/sql/schema-tier{B,C}.sql` (both cite `docs/PG-DREGG.md`
  in header comments), `sel4/dregg.system`'s XML comments (`docs/SEL4-EMBEDDING.md`,
  `docs/FIRMAMENT.md`), and 40+ `sel4/dregg-pd/*/Cargo.toml` build-mode justifications.
- **(c) 39 targets / ~50 lines — GONE, named not fixed** (per the lane brief's rule c: verify every
  target exists before repointing; did not fabricate). Two shapes:
  - **A coherent cluster that was never written**: `docs/engine/{review,design,probes}/*.md` (5 targets,
    ~17 lines) cited from `orb/Reactor/*.lean` (Stage/ConditionalRequest.lean, DateHeader.lean,
    FramingValidation.lean, etc.), `orb/GOAL.md`, `orb/conformance/FOOTGUN-MAP.md` — `docs/engine/`
    **does not exist at all** in this repo (checked: `ls docs/engine` → No such file or directory). These
    read as forward-references to docs that were planned but never authored, not renames.
  - **Scattered singles**, mostly `dregg-agent/src/*.rs` citing a `docs/HACKATHON-STACK.md`,
    `docs/BRING-YOUR-OWN-HARNESS.md`, `docs/VISION-NEXT-PRODUCT.md`, `docs/AGENT-RUNTIME-OPEN-SOURCE.md`
    that likewise never landed; `docs/deos/CONSENSUS-BINDS-INDEX.md` (5 lines, `dregg-query/src/client.rs`,
    `node/src/{api,state}.rs`); `docs/GRAIN-FORK.md`/`docs/GRAIN-VERIFY-HOME.md` — checked `grain-fork/`
    and `grain-turn/` for a moved doc, found only `README.md` in each, not a rename (the crates document
    themselves in-crate now, the top-level doc was apparently never split out). None of these have a
    plausible unambiguous target; each needs either the doc written or the citing claim revisited — an
    owner call, not a lane fix. Full 80-line list with file:line is in my scratch
    (`truly_final.json`) if wanted; not pasted here to keep this entry readable.

**NOT touched (dirty, reported not fixed) — 17 files, 30 dangling lines**, all mid-edit by other lanes:
`.github/workflows/ci.yml` (`docs/DESCRIPTOR-EMIT.md`), `circuit-prove/tests/proof_economics.rs`,
`circuit/src/{effect_vm/trace_rotated,effect_vm_descriptors,ivc,lib}.rs`, `dregg-lean-ffi/Cargo.toml`,
`dregg-query/Cargo.toml`, `grain-fork/Cargo.toml`, `grain-turn/Cargo.toml`, `perf/Cargo.toml`,
`sdk/src/full_turn_proof.rs`, `sel4/dregg-firmament/Cargo.toml`, `starbridge-v2/{Cargo.toml,src/world.rs}`,
`starbridge-web-surface/Cargo.toml`, `turn/src/executor/proof_verify.rs`. Their dangling refs are the same
two shapes as (a)/(b) above (e.g. `sel4/dregg-firmament/Cargo.toml` → `docs/FIRMAMENT.md` +
`docs/DREGG-DESKTOP-OS.md`, both archived-only) — mechanical once that lane lands, not a design call.

**Verification of the fix itself (not just "it ran"):** re-ran the full detection pass post-edit
(`git grep -nE` again, same boundary-aware resolver) → **80 dangling lines remain**, all accounted for by
the two buckets above (30 dirty-skipped + 50 genuinely-gone); **zero regressions** (diff-stat 640 files /
+7967/-3835, every sampled diff — `.rs` doc-comments, `.toml` build-mode headers, `.sql` header comments,
`.lean` module docs, `.system` XML comments — is a pure path-string substitution inside a comment/string
literal, never touching code; spot-checked ~10 diffs by hand + the double-prefix grep sweep above).
**Did not run a full `cargo check --workspace`** (contended target dir, out of this lane's budget) —
these are comment-only edits with no compilation surface, but flagging per the frame's own rule (build
what you change) rather than asserting it silently.

**Correction to the lane brief:** "Top offender: `docs/PG-DREGG.md` (89 lines)" undercounted — it was
**137 lines** (undercounting is exactly the class of error this whole campaign hunts, so noting it rather
than quietly using the bigger number).

Committed NOTHING — supervisor gates.

## 2026-07-17 — board/Lane C — DslComparisonRangeSoundnessResidual RESOLVED: the DSL comparison lowering is NOT range-check sound (PROVEN by a live prover)

**The question (from the corrected `dregg-dsl/src/lib.rs` doc):** the surviving DSL comparison path
(`<=`/`>=`/`in_range!`) — is a field-wrapped negative difference UNSATISFIABLE, or can a wrapped value
satisfy it? **Answer, established FROM CODE then pinned with a live prover: NOT SOUND — a wrapped value
satisfies it. The production p3 prover AND verifier ACCEPT a forged `5 <= 3`.**

**Ground truth traced (not inferred):**
1. `gen_air`'s `Constraint::RangeCheck { diff_col, bit_col }` (gen_air.rs:89-102) proves NOTHING. It is a
   TOPOLOGY descriptor (`dregg_dsl_runtime::AirConstraintSet`). Its only consumers are
   `dregg-dsl-differential/src/air_runner.rs` (matches the variant SHAPE, then re-derives accept/reject in
   NATIVE u64 via `check_le`) and structural token tests. **There is NO `AirConstraintSet -> CircuitDescriptor`
   converter anywhere in the repo** (grepped) — nothing lowers that descriptor into a proved constraint
   system. A single `bit_col` could not range-check a ~31-bit field difference anyway.
2. The ONLY DSL comparison that reaches a REAL prover is
   `dregg-dsl-differential/src/plonky3_runner.rs::drive_inequality`. It hand-builds a `CircuitDescriptor`
   ("diff-le", cols [smaller,bigger,diff,indicator]) and proves it through the PRODUCTION interpreter
   `dregg_circuit::dsl::dsl_p3_air::{prove_dsl_p3,verify_dsl_p3}`. Its ENTIRE constraint system:
   `C1: bigger - smaller - diff == 0` (mod p — always satisfiable), `C2: indicator*(indicator-1)==0`,
   `C3: indicator == 0`. **No bit decomposition bounds `diff`; nothing algebraically links `indicator` to
   `diff`.** The comparison's truth lives entirely in the HONEST WITNESS GENERATOR (native
   `ir_ok = smaller <= bigger`, which volunteers an invalid witness when the claim is false). A malicious
   prover just doesn't.

**THE FORGERY (proven live):** claim `5 <= 3` with witness `diff = (3-5) mod p = p-2`, `indicator = 0`.
Every constraint is satisfied → `prove_dsl_p3` produces a proof and `verify_dsl_p3` ACCEPTS it. The in-file
comment "we cap the diffs to a 30-bit range where this encoding stays sound" is FALSE — the forgery uses
far-sub-30-bit operands (5 and 3).

**Severity — a NAMED soundness gap, not a live production forgery:** the unsound lowering is the
DIFFERENTIAL HARNESS's own, not a shipped circuit. Consequence: the harness's Plonky3 "agreement vote" on
inequalities validates its witness generator, NOT its constraints — a genuinely unsound backend would still
pass the vote (same species as a soundness suite over a mock). Production circuits that need order
comparisons DO range-check genuinely — verified in code: `circuit/src/dsl/committed_threshold.rs` (C4 bit
reconstruction + C5 binary bits + `BoundaryDef::Fixed` forcing the top bit to zero), `derivation.rs`
C17/C22, `descriptors.rs` non-membership ordering. **No DSL surface currently lowers `<=`/`>=`/`in_range!`
into a proved circuit at all.**

**TOOTH RIGGED (permanent, mutation-verified):**
`dregg-dsl-differential/tests/comparison_wrap_soundness.rs` (4 tests, all green on persvati/srot):
- `honest_le_accepts_through_production_p3` — non-vacuity: a TRUE `3<=5` proves+verifies through the
  production interpreter (the pipeline is real).
- `rig_is_not_vacuous_inconsistent_diff_is_rejected` — PROVED THE RIG BITES: a `diff` violating C1
  (claim `3<=5`, diff=7) IS rejected, so the acceptance below is a real property, not a broken test.
- `honest_false_le_is_rejected_by_harness` — the harness rejects a false `5<=3` (but via the witness
  generator, per the finding above).
- `wrapped_negative_difference_forgery_is_accepted_known_unsound` — the CHARACTERIZATION PIN: asserts the
  wrapped-diff forgery IS accepted today. **If someone fixes the lowering (real bit-decomposition), this
  test goes RED — the signal to flip it into a rejection tooth and upgrade the doc from NAMED-UNSOUND to
  PROVEN-SOUND.** Explicitly documented NOT to be "fixed" by deletion.

Doc `dregg-dsl/src/lib.rs` "Range-check soundness" section updated NAMED -> RESOLVED (NOT SOUND), with the
test named and the production-circuit contrast recorded. Did NOT touch `plonky3_runner.rs` (held dirty by
another lane; only read it — my test reproduces its "diff-le" descriptor locally with a note to resync if
its shape changes).

Committed NOTHING — supervisor gates.

## 2026-07-17 — board/lane-a — `unexpected_cfgs` warn -> DENY, and 100/207 crates were never in the cage at all

**THE FINDING THE FLIP HID:** `[workspace.lints]` binds only crates with `[lints] workspace = true` —
and **100 of 207 members never opted in** (cargo-metadata census, not grep). The warn flip's "authoritative
list" only ever saw half the workspace; a phantom cfg in the other half would have warned at rustc's
default level and never been counted. Fixed structurally: appended the opt-in to **89** clean manifests;
added `unexpected_cfgs = "deny"` directly to the 6 with their own `[lints.rust]/[lints.clippy]` tables
(they can't ALSO set `workspace = true`); escalated starbridge-v2's existing declared-cfg entry
warn->deny (keeping its documented `zed-full-pane` check-cfg). Root `Cargo.toml` `unexpected_cfgs = "deny"`
with the coverage caveat written into the comment.

**SKIPPED (other lanes hold them dirty): `chain`, `deos-hermes`, `dreggnet-web`, `grain-turn`** — their
manifests were mid-surgery, so they are NOT bound by the deny (they keep rustc's default warn). Whoever
settles those crates: append `[lints]\nworkspace = true` (one liner each) to close the cage.

**VENDORED (targeted declarations, not blanket allows, not a workspace retreat):**
- `starbridge-v2/vendor/pathfinder_simd` — declared `cfg(pf_rustc_nightly)` (its build.rs emits it).
- `servo-render/vendor/servo-net` — declared `cfg(feature, values("test-util"))` (upstream feature the
  vendor trim dropped; surfaced as default-warn in run 1).
Path-deps get no cap-lints, so these would have warned forever; they can't fail the build (no opt-in).

**A REAL PHANTOM SURVIVOR, deny caught it on run 1 (rustc's list, not mine):** 3 sites in dregg-turn —
`#[cfg(any(feature = "prover", feature = "verifier"))]` at `bilateral_schedule.rs:733,813` +
`witnessed_receipt.rs:542`. **`verifier` was never a dregg-turn feature** (expected: default/prover/
threshold-sig) — the arm was ALWAYS FALSE. Consequence (the class's signature move): verify-only
consumers (`wasm`, `dregg-tui`, `sdk-ts/test/rust-verifier`, `starbridge-v2` — all
`default-features = false`, no `prover`) silently compiled OUT the rotated-WR schedule expansion in
`bilateral_bundle_pi` and hard-error on every rotated WitnessedReceipt — the OPPOSITE of the gate's
written intent ("the only feature configs that compile the aggregation path" — stale: `verifier` is
circuit's RETIRED feature namespace, and `bilateral_aggregation_air` is unconditional in dregg-circuit
now). FIX: removed the gates (everything referenced — `compute_turn_identity_pi`, `ExpectedBilateral`,
`sched` — is verify-floor, verified ungated); verify-only builds now get the expansion. Fail-closed gap,
not a forgery hole (it refused, it didn't accept).

**THE GREEN RUN UNMASKED 3 MORE ROT LAYERS** (cargo aborts-first, so each hid the next; all in CLEAN
files — missed consumers of other lanes' landed struct changes, fixed forward):
1. `demo/src/commit_state.rs:102` — 0-arg `delta.verify()` missed by the FoldDelta rewrite; now
   `verify(&old_state, &CheckPolicy::RuleNames(added_checks))` (the checks it admits are exactly the
   `rule:`-prefixed facts the same function builds via `make_rule`).
2. `tests/src/commitment.rs:378` (`fold_delta_with_tampered_removal_proof`) — same 0-arg call, invisible
   to plain `cargo check` (it's `#[cfg(test)]` — why the fold lane's check missed it); rewired to the
   builder's `state.clone()` pattern; ordering read from `fold.rs::verify` confirms
   `InvalidRemovalProof{0}` still the asserted variant (OldRootMismatch binds first, and old_root here
   is honest).
3. `perf/src/bin/perf_report.rs:220` — printed retired `TurnProofComponents::has_authorization` (field
   removed by the dirty sdk lane); dropped from the println. And
   `demo/real-dungeon-service/src/main.rs:315` — `StepReceipt` grew `decision_commitment`; this is a
   single-player `apply_choice` driver, so `None` per the field's own doc (the dreggnet-offerings
   initializers already carried it).

**PROOF OF GREEN (persvati srot, run 5):** `cargo check --workspace` AND `cargo check -p dregg-tests
--all-targets` both `Finished` — **0 errors, 0 `unexpected_cfgs` warnings anywhere** (scratchpad
deny-check5.log). Final hit list: EMPTY.

**TOOTH PROVEN TO BITE (mutation test):** planted `#[cfg(feature = "phantom_bite_proof_feature")]` in
`types/src/lib.rs` -> `cargo check -p dregg-types` FAILED with ``error: unexpected `cfg` condition value
... requested on the command line with `-D unexpected-cfgs` ``; removed the mutation (Edit, not
checkout) -> file byte-identical to HEAD (git-status clean) -> green in 1.14s.

Committed NOTHING — supervisor gates.

## 2026-07-17 — board/lane-F (rig the assumption surface) — the "every ed25519 site is strict" primitive-contract, RIGGED tree-wide (and one universal-forgery vector on the SLASHING path)

**The frame applied.** An assumption is only rigged if a test flags RED when the code drifts. The lane's
own headline pathology (`token/revocation.rs` non-strict ed25519 vs a STRICT Lean model, no test caught it)
is a PRIMITIVE-CONTRACT assumption: "every ed25519 verify is strict". I rigged it — two local mutation-proven
teeth on the highest-consequence attacker-key paths, plus the TREE-WIDE invariant the lane asked for (worth
more than ten local ones: it catches the NEXT drift).

**Ground truth FIRST (execution, not inference).** Built a standalone probe (`scratchpad/edprobe`) against
ed25519-dalek 2.2.0: a small-order verifying key (the identity point, compressed `y=1`) with signature
`(R=identity, s=0)` — `non-strict verify(): true` for EVERY message tested; `verify_strict(): false`.
`from_bytes` accepts the identity point (canonical), and `vk.is_weak()==true`. So under a cofactored verify,
an attacker holding NO SECRET forges a signature that passes — wherever the key is attacker-chosen.

### RIG 1 (FIXED code + mutation-proven tooth) — `dregg_blocklace::evidence`: a no-secret equivocation exhibit could SLASH a bonded strand

`EvidenceOfEquivocation` is a SELF-CONTAINED wire value — `verify()` reads `creator` out of the exhibit
itself (`blocklace/src/evidence.rs:165`), so the verifying key is fully attacker-chosen. It verified the
accused's Ed25519 half with the cofactored `vk.verify(...)` (`evidence.rs:108`). Consequence is real: this
predicate feeds `federation/src/court.rs::EquivocationEvidenceVerifier::verify` and `Court::resolve`
(`court.rs:98,228`), which SLASH the accused strand's bond. A small-order `creator` + `(R=identity,s=0)`
makes both headers "verify" over any conflicting content → a forged exhibit minted with no secret certifies
and slashes. FIXED to `verify_strict` at all three blocklace ed25519 verify sites: `evidence.rs:108`
(exhibit), `finality.rs:419` (block admission), `lib.rs:271` (hybrid block verify — the classical half).
Dropped the now-unused `Verifier` trait import from all three (finality/lib's remaining `.verify` are
`MlDsaPublicKey` inherent, not dalek). `blocklace` built warning-free.
- **Tooth (`evidence.rs:363 forged_exhibit_under_a_small_order_creator_refuses`)**: mints the identity-point
  forgery, asserts `vk.is_weak()` for NON-VACUITY (refused for weakness, not malformedness), same-slot +
  CONFLICTING content so `verify` cannot short-circuit, + a CONTROL that a genuine fork still certifies.
- **PROVEN TO BITE**: reverted `verify_signature` to `vk.verify(..)` → tooth FAILED
  `left: Ok(())` (the cofactored verify CERTIFIED the no-secret forgery); restored → 219/219 green.
  It is NOT redundant with the existing `forged_signature_refuses` (that forges under a different HONEST
  key, which the cofactored check refuses too — so it says nothing about strictness).

### RIG 2 (FIXED code + mutation-proven tooth) — `dregg_agent::receipt::verify_signature`: forged quorum co-signature

`verify_signature(signer, msg, sig)` (`dregg-agent/src/receipt.rs:243`) authenticates each independent
co-signer in a multi-sig quorum; `signer` is caller-supplied (in the quorum path it is `Attestation::signer`,
carried in the wire attestation). Its doc promises "a wrong signer ... `false` (fail-closed)". It used
cofactored `vk.verify(..)`, so a small-order `signer` forged a co-signer witness with no secret. FIXED both
sites to `verify_strict` (`:243`, plus the receipt-chain link verify at `:373`); dropped the `Verifier`
import.
- **Tooth (`receipt.rs:427 a_small_order_signer_cannot_forge_a_signature`)**: identity-point forgery over two
  distinct messages + `is_weak()` non-vacuity + a genuine-signature CONTROL.
- **PROVEN TO BITE**: reverted to `vk.verify(..)` → FAILED (cofactored verify accepted the no-secret forgery);
  restored → `cargo test -p dregg-agent --lib receipt::` 7/7 green.

### RIG 3 (NEW tree-wide gate) — `tests/tests/ed25519_strict_guard.rs`: the primitive-contract invariant, ENFORCED

The robust, compiler-grounded signal: `verify_strict` is INHERENT on `VerifyingKey`; the non-strict `verify`
is the `signature::Verifier` trait method and REQUIRES a trait import. A **module-top (column-0)**
`use ed25519_dalek::…Verifier` / `use signature::…Verifier` is the necessary condition for a non-strict dalek
verify at module scope — and test-mod / fn-local imports are indented, so they fall out automatically. The
gate walks every first-party production `src/**.rs`, flags a module-top non-strict `Verifier` import, and
requires each to be on a reviewed `ALLOWLIST`. Ground truth: **21 current hits, all classified** (the two
crates I fixed dropped their imports and are DELIBERATELY absent — a regression there re-adds the import and
turns the gate RED). Categories in the allowlist are honest, not blessing:
- `EXTERNAL-SCHEME MIRROR` (2, verified by reading): `bridge/src/solana_{consensus,wire}.rs` verify Solana
  vote-tx signatures under wire keys. **CORRECTION to the naive "every ed25519 is strict" premise: making
  these strict would be a BUG** — Solana's runtime uses cofactored verify; a strict bridge would REJECT votes
  the chain ACCEPTS (small-order keys are consensus-valid on Solana), diverging the bridge from the chain it
  tracks. Cofactored is correct there. (This is why a blanket invariant is unsound; the gate encodes the
  exception with its reason.)
- `TEST MODULE` (1): `turn/src/tests.rs` (`#[cfg(test)] mod tests;`).
- `HELD DIRTY` (2): `cell-crypto/src/peer_exchange.rs` (already `verify_strict` + already carries the
  small-order tooth from a prior lane — corroborates the technique), `federation/src/dkg_ceremony.rs`. Both
  uncommitted by other lanes — not touched (shared-tree rule).
- `GRANDFATHERED` (16): un-audited non-strict prod sites present before the gate — an honest DEBT LEDGER,
  each owing an attacker-key-reachability review (several — `dregg-agent/cred.rs`, `dregg-auth/credential/
  chain.rs`, `dregg-pay/{otc,swap}.rs`, `sdk/device_pairing.rs`, `webauth-core/credext.rs` — read as likely
  convert-to-strict: presented/wire keys). NOT claimed safe; the gate stops NEW ones and enumerates the rest.
- **NON-VACUITY shipped as a test** (`detector_is_non_vacuous`): the matcher MUST fire on the forbidden
  module-top import and MUST NOT fire on `VerifyingKey`-only or indented imports.
- **VERIFIED**: compiled + ran the gate standalone against the REAL tree (`rustc --test`, CARGO_MANIFEST_DIR
  pinned): both tests PASS (`2 passed`; the gate walk found exactly the 21 allowlisted, 0 violations, 0
  stale). Cross-checked the walk with a faithful Python mirror (21 hits, 0 viol, 0 stale). BITE proven by
  mutation: a simulated blocklace regression (`use ed25519_dalek::{Verifier, VerifyingKey};`) fires the
  detector AND is a violation (blocklace is not allowlisted). The `dregg-tests` crate is heavy (links the
  workspace) and its full `cargo test` build did not finish in-session; my test file is std-only so it cannot
  introduce a compile error of its own — the standalone `rustc --test` run IS the executable proof.

### NAMED — irreducible / owner-decisions (not fake-rigged)
- **Pure-math carriers stay irreducible**: `SchnorrDLHard`, `Ed25519EufCma`, `ForkingExtractor` are correctly
  Props whose negation is a solver — NOT test-riggable, and I did not fake-rig them. The validation question
  for that class is "does the deployed Rust implement the scheme the carrier is about" — exactly the gap the
  strict/non-strict drift sat in. This gate is one systematic answer for the ed25519 carrier.
- **16 GRANDFATHERED sites owe an audit** (above). The high-suspicion convert-to-strict set is named; I did
  not convert them because each needs a per-site key-source read + a crate build I could not all verify this
  session (and `node/src/{relay_service,identity_export,api}.rs` carry the SAME native attacker-key shape but
  `node` has a standing build blocker — `dregg-lean-ffi/build.rs` arity — so I did not blind-edit it).
- **CI wiring**: the gate runs as a normal `dregg-tests` test (like `verify_routing_guard.rs`). I did NOT
  wire it into `.github/workflows/ci.yml` — that file is held dirty by another lane. Supervisor: ensure the
  `dregg-tests` test target runs in CI so this gate (and the routing guard) actually execute.

**Files (mine, all clean on arrival — verified against the session-start dirty snapshot):**
`blocklace/src/{evidence,finality,lib}.rs`, `dregg-agent/src/receipt.rs` (NOT its Cargo.toml — that was dirty,
untouched), new `tests/tests/ed25519_strict_guard.rs`. **Committed NOTHING — supervisor gates.**

## 2026-07-17 — board/lane-E (zero-use pub items) — 15 dead pub items DELETED (−796 LOC), one drifted MIRROR among them; 8 named-not-deleted incl. a doctest carrier my grep called dead

**Method (the greps-lie discipline, mechanized then hand-verified):** enumerated 7,294 bare-`pub` items
(5,995 unique names) across the 8 core crates, one repo-wide rg pass per name-chunk over ALL file types
(tests/src + teasting/ are crates; sdk-ts/sdk-py bind rust — all included), per-line classified: def /
`pub use` (NOT a consumer) / comment (NOT a use) / `impl Name` (the item's own body) / plain-`use`+everything-else
(= consumer, conservative). 225 zero-use candidates survived (the board's 328 was a coarser count). Ranked
by removable LOC (brace-matched spans incl. docs/attrs); every deletion target then got an individual
`rg -n "\bname\b" .` whose full output was ONLY the def (+ doc mentions, each fixed) — recorded in-session.

**DELETED (15 pub items, +3 private orphans the compiler/warnings named; net −796/+36 lines, all files
clean-or-citation-only at edit time):**
1. `RotatedParticipantLeg::mint_from_block_witnesses` (circuit-prove/joint_turn_aggregation.rs, 101 LOC) —
   **a drifted MIRROR, not mere dead code**: `turn/rotation_witness.rs::mint_rotated_participant_leg`'s doc
   claimed it "hands witnesses to the pure-circuit core" — it REIMPLEMENTS the body inline, and the dead
   "core" hard-codes `None` where the live path threads `sender_membership_teeth(before_cell)` (its legs
   would be REFUSED by the fold's membership arm on transfer turns). Same species as the deleted DslP3Air
   shadow. Docs rewritten to the truth at rotation_witness.rs + the welded-mint sibling doc +
   umem_boundary_producer.rs. RESIDUAL: `sdk/src/full_turn_proof.rs:1188` doc still cites the corpse —
   file held dirty by another lane, not touched.
2. `generate_extended_garbled_trace` (circuit/dsl/garbled.rs, 121) + 3. `comparison_records_to_extended`
   (17) — the garbled-DSL prove side; nothing in-tree ever minted a garbled trace. garbled_air.rs's
   deprecation note (which pointed users AT the deleted fn as the migration path) corrected.
4. `generate_adjacency_trace` (circuit/membership_adjacency_air.rs, 109) + private `bit`/`col`/`walk`
   helpers + 3 orphaned imports — the hand-rolled adjacency prove side (the emitted-descriptor path is the
   live one; `verify_adjacency` untouched).
5. `temporal_absence_dsl_circuit` + 6. `generate_temporal_absence_trace` (circuit/dsl/temporal_absence.rs,
   72) — prove side; the witness types dregg-dsl-runtime re-exports stay.
7. `generate_committed_threshold_trace` (circuit/dsl/committed_threshold.rs, 47) + its dsl/mod.rs re-export
   (a re-export is not a consumer; both deleted).
8. `Authorization::to_auth_kind` (turn/action.rs, 33) — an UNWIRED MIRROR of the permission lattice: the
   real dispatch is `check_single_auth_requirement`'s direct match; the comment at executor/authorize.rs:218
   cited `to_auth_kind() == Signature` as the mechanism — a citation lie, rewritten to name the real arm.
9. `observe_vault_lock_consensus_anchored` (bridge/solana_relayer.rs, 28) — zero-caller vault wrapper whose
   sibling doc called it "the production path" while production actually calls
   `observe_lock_at_consensus_anchored` (:1558); the pinned-anchor security doc MOVED to the live method,
   the test-gated weak variant's doc now points at the real production entry.
10. `authorize_with_custom_rules` (bridge/authorize.rs, 25). 11. `compile_nor` + private `flip_predicate`
   (circuit/predicate_program.rs, 104) — NOR was never reachable. 12./13. `deep_nested_gate_tree` /
   `three_level_gate_tree` (circuit/dsl/predicates/compound.rs, 39). 14. `CanonicalCapTree::num_caps`
   (circuit/cap_root.rs, 20; filter-semantics doc folded into `live_and_tombstones`).
   15. `EpochMinter::estimated_annual_issuance` (turn/economics.rs, 18).

**VERIFIED:** persvati `cargo check --workspace` (excl. `real-dungeon-service`, red from ANOTHER lane's
in-flight `StepReceipt.decision_commitment` deepening — their fix sits dirty in-tree) → **Finished, ZERO
errors/warnings in any file I touched** (all-targets pass too, see below). `mock_proof_purge_gate` → ok.

**FALSE POSITIVES my scan produced — the method lesson, again:** (i) `sdk/cipherclerk.rs::_Marker` scored
28 dead LOC — it is the `#[cfg(doctest)]` CARRIER of three `compile_fail` sealed-value gates; the doc
comments ARE the test. A doc-comment-is-not-a-use heuristic calls the one construct whose docs are
load-bearing "dead". Kept. (ii) My first import cleanup over-deleted `ColumnDef`/`ColumnKind` (rustc's
unused list for a DIFFERENT file read as this file's) — the compiler caught it; trust rustc's file:line,
not pattern-matched warning text.

**NAMED, NOT DELETED (deliberate surface / ambiguous / held-dirty):**
- `prove_{shielded_spend_root,caveat_admission,note_spend}_binding_node_segmented` (~270 LOC, zero use) —
  each is a documented "ready consumer" of a NAMED VK-gated big-bang seam (ABI §4.1(b) exposure regen);
  prepared machinery, not corpses. (Bridge sibling: file held dirty.)
- `Turn::with_custom_program_proofs` (49) — the only correct attach-side packing for the live, hash-bound
  `custom_program_proofs` wire field (`enforce_custom_effect_proofs` is the live verify side); every
  in-tree producer writes `None`, so the FEATURE has no first-party producer — an owner question, not a
  deletion.
- `verify_presentation_nonce` (bridge/present.rs, 31) — documented challenge-response replay protection
  that NOTHING calls, and the prover hard-codes `verifier_nonce = ZERO` ("TODO: accept from verifier
  challenge") — the whole nonce mode is unbuilt; wire-or-retire is ember's call.
- `CanonicalCapTree::delegation_witness` (26) — Phase-B2-documented staged machinery.
- `dregg-sdk` surface left alone on principle (e.g. `derive_keypair_bip39_compat`, `plan_trustline`,
  `explain_and_sign_turn`): SDK exports with zero in-tree callers may serve external consumers.
- Held-dirty at arrival (zero-use but untouchable): `prove_bridge_binding_node_segmented` (86, joint_turn_recursive),
  `derivation_authorizing_effects` (79) / `effect_action_binding` (46) / `rotated_prover_enabled` (20)
  (sdk/full_turn_proof.rs), `verify_proof_carrying_turn_bundle_with_ledger` (40, executor/proof_verify.rs),
  `is_known_dsl_air` (17, dsl/descriptors.rs), ivc.rs remnants. Mid-session real edits arrived in
  presentation.rs (Lane B's TraceSummary rewrite) and witnessed_receipt.rs (phantom-`verifier`-cfg ungating),
  so `PresentationBuilder`+3 helpers (~140) and `from_components_strict_recursive` (23) were dropped from
  my delete set and belong to a later pass. Remaining ~200 candidates: scratchpad ranked.json (session dir).

**PRE-EXISTING BREAKS SURFACED (not mine — proven against HEAD):** `--all-targets` shows
`demo-agent/examples/garbled_ot_auction.rs` imports `prove_private_threshold_dsl`/`verify_private_threshold_dsl`
and `private_auction.rs` imports `PredicateProof`/`prove_predicate`/`committed_threshold::prove_committed_threshold`
— NONE of these exist anywhere at HEAD (`git show` grep = zero defs). Two more never-compiled examples of
the "nobody ever compiled it" class. Also: **law1_enforcement_gate is RED independently of me** —
`circuit/src/custom_leaf_lowering.rs` (46 NEW sites) was COMMITTED at `21e2c58d0` without a baseline story,
and dirty `joint_turn_recursive.rs` grew 2→6 sites (another lane, in flight). My deletions only shrink
listed files, which the ratchet explicitly allows.

**Shared-tree note:** mid-session the tree went 155→684 dirty files (Lane D's mechanical
`docs/*.md → .docs-history-noclaude/` citation sweep). For the 3 of my files carrying such diffs
(action.rs, predicate_program.rs, rotation_witness.rs) I verified their changed lines (5, 3, 410/1484) are
disjoint from my spans before editing. **Committed NOTHING — supervisor gates.**


## 2026-07-17 — board/lane-B — the "constraint PROVER" that proves nothing is renamed to VALIDATOR; consumer census found ZERO surfaces treating its digest as a proof

**Verdict from CODE (not comments): `constraint_prover.rs` is an HONEST LOCAL VALIDATOR with a lying NAME.**
Its own doc (:5-8) already confessed "a trace digest ... **not** a cryptographic proof ... nothing here is
sound against a prover that lies." The lane question was whether any real consumer treats its output as a
PROOF. Answer, from a full workspace census (no `/tests/`-exclusion this time — `tests/src` IS the
`dregg-tests` crate): **nobody does.** So the fix is the `*_air`-on-a-non-AIR fix — make the NAME tell the
truth — not a rewire, because there was no lie in the wiring, only in the identifiers.

### The consumer census (every non-comment ref to `ConstraintProver`/`ConstraintProof`/`generate*`)
- **`ConstraintProver::verify` / `verify_trace`** — a row-by-row AIR constraint check on a caller-supplied
  trace. Real callers: `circuit/src/presentation.rs` (`PresentationAir::prove`/`verify_all`),
  `circuit/src/tests.rs`, `bridge/src/present.rs` + `bridge/src/tests.rs` (both `#[cfg(test)]`),
  `tests/src/soundness.rs`. **Every one is legitimate LOCAL validation** — prover-side witness sanity or a
  test exercising an AIR's constraint set. None is a cross-trust-boundary "verify".
- **`ConstraintProof` (the digest struct)** — appears ONLY inside `PresentationProof.{fold_proofs,
  derivation_proof, issuer_membership_proof}`, which rides `WirePresentationProof` on the wire. I traced
  ALL production verifiers of that wire: `dregg_bridge::present::{verify_proof_complete,
  verify_presentation_full, verify_presentation_bb, verify_presentation_complete}`. **Not one reads a
  `trace_digest`.** They require + cryptographically verify the SEPARATE `real_stark_proof` descriptor
  wires (`verify_descriptor_wire` → `descriptor_by_name` → `verify_vm_descriptor2`), and read only
  `circuit_proof.public_inputs` as metadata to bind against the STARK's own PIs. `is_valid()`
  (`present.rs:334`) rests solely on `real_stark_proof.is_some() && verification==Valid`. The digest is
  DEAD METADATA. (The wire even carries a self-labelled `AUDIT[P3]` footgun — a prover-set `verification`
  field — and the audit note already confirms `verify_proof_complete` ignores it.)
- **`generate_unchecked`** — one caller: `PresentationAir::prove` for issuer membership (the witness uses a
  different hash than `MerkleAir`, so the local check is deliberately skipped; the real check is the
  Poseidon2 STARK). Honest.
- **`ProofTier::Structural` / `constraint_prover_tier()` / `CONSTRAINT_PROVER_BACKEND`** — the tier that
  named this a "backend." **Zero callers** for the fn and the const (grep-confirmed).
- **`PresentationProof::verify` (the plaintext meta-check)** — **zero production callers** (only
  `circuit/src/tests.rs`). It compares prover-authored PIs against each other; a lying prover satisfies it
  trivially. Left in place, doc corrected to say NOT-cryptographic + zero-production-callers.

### FIXED (rename to honest names; the artifact is byte-identical, only identifiers changed)
- `circuit/src/constraint_prover.rs`: `ConstraintProver → ConstraintValidator`, `ConstraintProof →
  TraceSummary`; module + type docs rewritten to state plainly it is LOCAL validation with no adversarial
  soundness and that no workspace verifier reads the digest. Deleted the dead `ConstraintProof::verify`
  (renamed to `TraceSummary::public_inputs_match` — it was a plaintext PI compare misnamed "verify") and
  the unused `proof_size_display`. Legacy `type` aliases (`ConstraintProver`/`ConstraintProof`/`Mock*`)
  kept `#[doc(hidden)]` ONLY because `circuit/src/lib.rs` (held dirty by another lane) re-exports them by
  name — retire the aliases when lib.rs is free.
- `circuit/src/presentation.rs`: migrated to the new names; `PresentationProof` struct doc now states the
  three fields are NOT proofs and names where the real crypto lives; `prove`/`verify_all`/`verify` docs
  corrected from "prove/verify" to "locally validate/summarize."
- `circuit/src/proof_tier.rs`: DELETED `constraint_prover_tier()` + `CONSTRAINT_PROVER_BACKEND` (zero
  callers, and they advertised the validator as a proof backend); `Structural` tier doc now says no live
  producer constructs it.
- Test-mod consumers migrated: `circuit/src/tests.rs` (`mock_prover::MockProver` → `ConstraintValidator`),
  `bridge/src/present.rs` + `bridge/src/tests.rs` (`ConstraintProver::verify` → `ConstraintValidator`).

### RATCHET lowered + PROVEN TO BITE
`circuit-prove/tests/mock_proof_purge_gate.rs`: widened `count_mock_sites` to count BOTH `ConstraintProof`
(surviving alias) AND the new `TraceSummary` (identical artifact, so the gate cannot be dodged by the
rename), and SHRANK the `constraint_prover.rs` baseline **17 → 15** (dead `proof_size_display` gone). Module
doc updated to record the rename + the census verdict.
- **Bite proof**: dropped a scratch `circuit/src/zz_lane_b_bite_probe.rs` containing the string
  `"TraceSummary"` → gate went RED: `NEW production surface rides a MOCK prover: .../zz_lane_b_bite_probe.rs
  (1 sites)`. Removed the probe → GREEN again. The widened pattern set is what makes the rename un-dodgeable.

### VERIFIED (persvati `srot`)
- `cargo test -p dregg-circuit --lib constraint_prover::tests` → **4 passed** (renamed
  `constraint_validator_*` + `trace_summary_*`).
- `cargo test -p dregg-circuit --lib tests::` → all presentation/fold/merkle/e2e tests pass
  (`end_to_end_authorization_proof`, `long_attenuation_chain`, `single_step_no_attenuation`, etc.) — the
  `verify_all`/`prove`/`verify` path through the renamed validator.
- `cargo test -p dregg-bridge --lib present::tests` → **21 passed** (the presentation build/verify surface).
- `cargo check -p dregg-bridge --all-targets` → **Finished** (clean); `cargo check -p dregg-tests
  --all-targets` → **Finished**.
- `mock_proof_purge_gate` → **ok**; bite-probe RED-then-GREEN as above.

### NOT MY BREAKAGE (named, other lanes' in-flight descriptor rename)
Pre-existing failures NOT caused by this rename (a semantically inert identifier change cannot alter a
descriptor identity string or Ethereum calldata):
- `circuit` lib: `effect_vm_descriptors::tests::provenance_json_pins_match_checked_in_descriptor_bytes` —
  `circuit/src/effect_vm_descriptors.rs` is DIRTY (another lane); descriptor-sha256 pin drift.
- `bridge` lib: `present::ir2_issuer_wire_roundtrip::*` (3) assert descriptor identity
  `"merkle-membership::poseidon2-4ary-general-depth4"` but code now emits
  `"dregg-merkle-membership-4ary-general::v1"` — a descriptor-name rename in flight elsewhere; and
  `ethereum::tests::real_fixture_settle_calldata_matches_foundry_ground_truth` (calldata ground-truth).
  None touch `constraint_prover`/`presentation` type names.

### SKIPPED as dirty (reported, not edited)
`circuit/src/lib.rs` (held dirty; still re-exports the legacy `ConstraintProof`/`ConstraintProver`/`Mock*`
names — kept working via the doc-hidden aliases), `circuit/src/dsl/mod.rs` +
`circuit/src/membership_adjacency_air.rs` (a dead-code-removal lane, briefly broke the circuit build
mid-session then settled), `circuit/src/effect_vm_descriptors.rs`. `tests/src/soundness.rs` uses
`mock_prover::MockProver` but is gated behind the `__legacy_tests` feature (declared in `tests/Cargo.toml`
but never enabled — the module NEVER COMPILES, a separate known husk; the `RemovedFact` fields it
constructs (`membership_verified`, no `added_checks_commitment`) do not even match the real struct). Left
untouched; the doc-hidden `MockProver` alias keeps it name-resolvable if that feature is ever turned on.

**Committed NOTHING — supervisor gates.**
