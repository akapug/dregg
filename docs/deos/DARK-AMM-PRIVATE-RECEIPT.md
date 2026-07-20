# Dark AMM private transition receipt

Status at HEAD (2026-07-19): implemented as a Lean-authored fixed-family IR-v2
descriptor and a witness-hiding HidingFri prover/verifier.

This receipt proves one exact constant-product transition without publishing
either reserve or either trade amount. It is the proof-authoritative transition
path for the Dark Bazaar AMM; the FHE path may find candidate transitions, but
does not get to redefine what a valid transition means.

## Statement and witness

The 19 public BabyBear values, in canonical order, are:

```text
[session, rule, k, oldRoot[0..8), newRoot[0..8)]
```

The private witness carries `x`, `y`, `dx`, `dy`, eight old-state blind limbs,
and eight new-state blind limbs. The AIR derives `postX` and `postY`; they are
not independently supplied public state.

The fixed family enforces:

- `x`, `y`, `dx`, and `dy` are canonical ten-bit integers;
- `postX` is an eleven-bit integer and `postY` is a ten-bit integer;
- `dx > 0`, `dy > 0`, and `dy <= y`;
- `postX = x + dx` and `y = postY + dy`;
- `x * y = k` and `postX * postY = k`; and
- `oldRoot` and `newRoot` are all eight output lanes of full-arity Poseidon2
  permutations over the exact semantic preimages in
  `Market.DarkAmmPrivateReceipt`. Both use one state-commitment domain, so an
  accepted `newRoot` is the next receipt's exact `oldRoot` when the producer
  carries the new blind forward.

The descriptor has 104 trace columns, 19 public inputs, and 169 constraints.
Its checked-in JSON is byte-for-byte the output of `EmitByName.lean`.

## Formal boundary

`Market.DarkAmmPrivateDescriptor.darkAmmPrivate_descriptor_to_accepts` proves:

```text
canonical trace + canonical PIs
+ Satisfied2 emitted descriptor
+ sound wide Poseidon chip table
=> Market.DarkAmmPrivateReceipt.Accepts
```

The proof includes exact, wrap-free integer decoding of every scalar range and
both product equations. Nineteen load-bearing theorems are pinned with
`#assert_all_clean`.

## Runtime boundary

`dregg-circuit-prove::dark_amm_private` exposes only the privacy-facing API:

```rust
PrivateAmmWitness::try_new(...)
statement(session, &witness)
prove_zk(session, &witness)
verify_zk(&proof, public_statement)
```

There is deliberately no privacy-ambiguous default prover and no non-hiding
compatibility function in this module. Each proof call constructs a fresh
OS-seeded `DreggZkStarkConfig`, so salted commitments, random trace rows, and FRI
codewords are independently randomized.

Negative tests refuse a wrong quote, an overdraw, zero amounts, noncanonical
blind limbs, and verifier-side mutations of `k`, either old-root state lane, or
either new-root state lane.

## Hosted Dark Bazaar weld

`dreggnet-market::dark_amm_game` has two deliberately distinct modes. The
legacy operation remains `dark-bazaar.private-amm-swap.v1` and is never painted
as proved. A table created with `demo_proof_required` or
`configured_proof_required` exposes only
`dark-bazaar.private-amm-swap.proved.v2`.

The v2 canonical request carries the exact 19-felt statement, opaque canonical
HidingFri proof bytes, and BFV ciphertexts for `dx` and `dy`. Before mutation,
the host requires the statement's session, rule, `k`, and old root to equal its
current public context and verifies the hiding proof. It then runs the existing
encrypted candidate/decision path. Only when both gates succeed does it advance
the encrypted pool, new root, sequence, and accepted-operation journal. The
public receipt and durable replay record retain statement/proof/request digests;
restart replay re-verifies both gates and the complete root chain.

The shared hosted-operation adapter makes this same operation discoverable and
uploadable through web, Telegram Mini App, and Discord Activity surfaces.
`dark-amm-tool proved-swap` accepts an already-produced statement file and raw
proof postcard; it has no private witness input. Deployments opt into v2 by
setting `DREGG_DARK_AMM_INITIAL_ROOT` to eight comma-separated BabyBear lanes
alongside the protected BFV key.

## Offline private producer lifecycle

The primary proof-required lifecycle needs no caller-authored Rust and does not
ask an operator to copy a hidden opening onto a command line after bootstrap.
For the fixed demo reserves `(100,900)`:

```sh
dark-amm-tool keygen dark-amm.key
dark-amm-tool public-id dark-amm.key web-session-17 bootstrap.dbap
dark-amm-tool private-init bootstrap.dbap 100 900 state-0.dbao
dark-amm-tool public-id-private \
  dark-amm.key web-session-17 state-0.dbao proof-0.dbap
dark-amm-tool private-swap \
  proof-0.dbap state-0.dbao 50 300 200 400 swap-0
```

`state-0.dbao` is a fixed-width, versioned, checksummed private custody object
containing the full hosted session id, receipt-session projection, `k`, hidden
reserves, and current commitment blind. The CLI accepts it only as a regular,
non-symlink file with no group or other permissions. `public-id-private` refuses
a different session or invariant and constructs the proof-required public
context at the state's exact root.

`private-swap` reuses the current blind as the proof's old opening, samples a
fresh successor blind, proves the exact transition, and encrypts that witness's
same `dx` and `dy`. It atomically publishes one owner-only directory containing:

- `request.dbam` — the canonical proved-v2 body later wrapped into the hosted
  v3 request after issuer endorsement;
- `statement.dbas` — the exact public receipt statement;
- `next-state.dbao` — the successor private opening; and
- `authority.dbaa` — private Tier-1 endorsement material.

The authority wire retains the full witness and independent BFV encryption
seeds, plus digests of the exact statement, proof, and request. Each ciphertext
is produced by a fresh `rand_09::rngs::StdRng` from its retained seed, matching
fhEgg's `ExactBfvAmountOpening` construction. Revalidation reconstructs both the
statement and byte-identical ciphertexts, so the already-produced request can
later receive the §34 same-opening endorsement without reproof or re-encryption.
The file exposes the private transition to any issuer given access to it and
must not be uploaded or journaled as public material.

Only after `request.dbam` is accepted should the operator promote
`next-state.dbao` and advance the public cursor:

```sh
dark-amm-tool proved-cursor \
  proof-0.dbap swap-0/statement.dbas 1 proof-1.dbap
dark-amm-tool private-swap \
  proof-1.dbap swap-0/next-state.dbao 150 300 200 400 swap-1
```

A refused upload leaves the old state and cursor authoritative. Existing
`public-id-proved`, `proved-swap`, and `proved-cursor` commands remain available
for advanced producers that already have statement and proof artifacts.

## What this does not claim

This is a Tier-1, operator-visible receipt. The process constructing the trace
sees the private transition. The proof hides it from proof consumers.

The integrated producer uses one witness and retained deterministic BFV
openings, which removes accidental honest-producer divergence. The host now has
two deliberately different proof policies. `proved.v2` retains the older
independent proof/BFV checks and its same-opening residual. Strict
`proved.same-opening.v3` accepts only a canonical wrapper containing that exact
v2 body plus the verified Tier-1 receipt; it reconstructs and pins the BFV key,
ciphertexts, proof, statement, session, sequence, roots, `k`, and issuer policy
before mutation, and commits receipt replay with the encrypted/root transition.
There is no v2 fallback in a v3-configured offering.

The library exposes `DarkAmmPrivateSwapAuthority::endorse_same_opening` and
`assemble_same_opening_request` for issuer services. The offline CLI exposes
those as two distinct artifact steps. An ordered roster file is the raw
concatenation of 1–16 Ed25519 public keys (32 bytes each); the threshold and
signer index are explicit command arguments. Issuer secret-key files are
exactly 32 raw bytes and, like `authority.dbaa`, must be regular non-symlink
files with no group/other permission bits.

```sh
# Run independently in issuer 0's and issuer 2's custody environments.
dark-amm-tool same-opening-endorse \
  proof-0.dbap swap-0/request.dbam swap-0/authority.dbaa \
  issuers.roster 2 0 issuer-0.key issuer-0.fhase
dark-amm-tool same-opening-endorse \
  proof-0.dbap swap-0/request.dbam swap-0/authority.dbaa \
  issuers.roster 2 2 issuer-2.key issuer-2.fhase

# The owner/producer assembler retains its authority bundle, receives only the
# public endorsement artifacts from issuers, and emits the uploadable v3 body.
dark-amm-tool same-opening-assemble \
  proof-0.dbap swap-0/request.dbam swap-0/authority.dbaa \
  issuers.roster 2 request-v3.dbam issuer-0.fhase issuer-2.fhase
```

Each `FHASE003` endorsement is fixed-width and contains one canonical
`FHASO003` claim plus exactly one signer record—never the witness, encryption
seeds, or signing key. The decoder refuses the wrong version, every truncation,
trailing bytes, malformed claims, and an out-of-roster signer. Assembly verifies
the signatures, requires one identical claim and the configured threshold,
canonicalizes signer order, and pre-verifies the complete v3 request. Duplicate,
subthreshold, claim-substituted, wrong-roster, wrong-index, and wrong-key inputs
fail before output publication. Both commands use atomic create-new output and
never print secret material.

This reference deployment still gives every participating Tier-1 issuer the
complete private transition and both deterministic BFV seeds through
`authority.dbaa`; it separates issuer keys and artifacts but is not MPC witness
custody. The owner-side assembler already owns that authority bundle. A remote
service should transport it over a protected issuer channel and return only the
endorsement artifact.

The v3 same-opening claim also authenticates the full canonical BFV parameter
digest (including error variance) and the exact public `dx_bound` and
`dy_bound` used by the BFV evaluator. Each issuer refuses zero bounds, bounds at
or above the plaintext modulus, or a bound below the opened amount. Thus a
producer cannot retain the same ciphertext/proof while underdeclaring a cap to
invalidate the evaluator's no-wrap reasoning. This is a wire-version migration:
old `FHAS{O,E,R}001` and `FHAS{O,E,R}002` artifacts fail closed.

The receipt does not supply no-single-viewer threshold custody and is not by
itself a custom-VK state-cell transition. Current hosted BFV custody remains
visibly `n=1/opening_threshold=1`; the one host technically can decrypt reserves
and amounts. Active asset settlement is deliberately outside this demo
operation.

## Narrow gates

```sh
cd metatheory
lake env lean Market/DarkAmmPrivateDescriptor.lean

scripts/pbuild botverify env DREGG_REQUIRE_LEAN=0 \
  cargo check -p dregg-circuit-prove --lib --release
scripts/pbuild botverify env DREGG_REQUIRE_LEAN=0 \
  cargo nextest run -p dregg-circuit-prove --lib --release private_amm
scripts/pbuild botverify env DREGG_REQUIRE_LEAN=0 \
  cargo nextest run -p dreggnet-market --features dark-amm-game \
  --test dark_amm_private_tool --release
scripts/pbuild botverify env DREGG_REQUIRE_LEAN=0 \
  cargo nextest run -p dreggnet-market --features dark-amm-game \
  --test dark_amm_same_opening_tool --release
```

The release prover gate is two tests. The private lifecycle integration chains
two real hiding-proof transitions and exercises wrong session/state, invalid
quote, stale state, owner-permission, checksum-tamper, and output-collision
refusals. The same-opening CLI lifecycle gives the owner bundle to two separate
issuer invocations, parses both strict endorsement artifacts, refuses a wrong
signer key, duplicate signer, and overwrite, assembles v3, and submits that exact
wire through the real game operation.
