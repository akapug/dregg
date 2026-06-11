# Proof Economics

What each proof artifact in dregg costs — bytes on the wire, prover seconds,
verifier seconds — which knobs control those costs, who actually has to
receive each artifact, and what the Kimchi/Pickles interop lane can and cannot
buy. Every number in this document is measured, on an Apple-silicon dev
machine, release profile, by `circuit/tests/proof_economics.rs` and
`circuit/src/backends/poseidon2_bb_kimchi.rs`:

```
cargo test -p dregg-circuit --release --test proof_economics -- --nocapture
cargo test -p dregg-circuit --release --test proof_economics -- --ignored --nocapture   # IVC folds
cargo test -p dregg-circuit --release --lib backends::poseidon2_bb_kimchi -- --nocapture # bridge spike
```

## 1. What we ship (the size table)

| artifact | wire encoding | size | prove | verify | config |
|---|---|---:|---:|---:|---|
| per-turn EffectVM descriptor proof (`EffectVmP3Proof`, label `effect-vm`) | postcard | **451.7 KiB** (462,537 B) | ~0.3 s | 22 ms | `create_config` (lb=3, q=50, pow=16) |
| joint-turn, per participating cell | postcard | 451.7 KiB each | ~0.3 s each | 22 ms each | same |
| joint-turn Silver apex (width-4 aggregation `BatchProof`) | postcard | ≲ per-turn (same FRI shape, far narrower trace) | — | — | same |
| whole-chain IVC ROOT (`WholeChainProof.root`, K=2) | postcard | **46.4 KiB** (47,538 B) | 5.0 s fold | **2 ms** | recursion config (lb=3, **q=2, pow=0**) |
| whole-chain IVC ROOT (K=3) | postcard | 46.4 KiB (47,519 B) | 7.6 s fold | 2 ms | same |
| + carried chain-binding proof (K=2 / K=3) | postcard | 1.3 / 1.9 KiB | — | included | same |
| + the verifier's trust anchor (`RecursionVk`) | out-of-band, once | 32 B | — | — | — |

The browser-measured ~452–497 KiB per-turn proof is confirmed: 451.7 KiB is
the postcard encoding of the transfer-descriptor proof; other effect
descriptors vary a few KiB with hash-site/range-column counts.

Where the per-turn bytes live: the FRI opening proof is 426.7 KiB (92%) of the
artifact; opened out-of-domain values are 24.9 KiB; commitments are 81 B. The
opening proof is dominated by the 50 query openings, each of which opens a
full extended-trace row (**1,654 columns**: 186 base EffectVM columns + 4
Poseidon2 hash-site aux blocks of 352 columns each + range-bit columns) plus
its Merkle path — ≈ 8.5 KiB per query.

The ROOT proof is **K-independent**: K=2 and K=3 both serialize to 46.4 KiB
and verify in 2 ms. This is the genuine IVC property — the root's cost is the
root verifier-circuit's, not the history's.

## 2. The knobs (measured grid)

All rows prove the SAME transfer-descriptor statement. "conj bits" is the
conjectured FRI soundness `num_queries x log_blowup + pow` (capacity-bound
conjecture); proven (Johnson-bound) soundness is roughly half the query term.
Prove/verify times at this trace size (64 rows) are small and noisy — read
them as direction, not precision.

| knob | bytes | Δ size | prove | conj bits | note |
|---|---:|---:|---:|---:|---|
| **production today** (lb=3, q=50, pow=16, arity=2³) | 451.7 KiB | — | 34 ms | 166 | ~91 proven |
| q 50→38 | 349.3 KiB | **−23%** | ~same | 130 | the 128-bit-conjectured point; prover cost unchanged (queries only affect opening) |
| lb 3→4, q=28 | 268.3 KiB | **−41%** | ~6x commit | 128 | smallest at 128-bit conj; prover pays the doubled LDE |
| lb 3→4, q=38, pow=14 | 355.2 KiB | −21% | ~3x | 166 | same headline security as today, smaller, slower prover |
| final-poly 2⁰→2⁴ early stop | 437.5 KiB | −3% | ~same | 166 | marginal |
| fold arity 2³→2¹ | 490.5 KiB | +9% | slower | 166 | confirms arity-8 folding is already right |

**No clearly-free change exists**, so none is made. The two candidates and
what each actually trades:

- **q=50→38 (−23%, zero prover cost)** is free *only if* the declared
  security target is 128-bit conjectured. Today's q=50 gives 166-bit
  conjectured / ~91-bit proven; nothing in the tree declares which of those
  is the contract. Dropping queries is a one-line change to
  `create_config` but changes the proof shape (a VK/commitment bump across
  every consumer), so it should ride a planned bump once the target is
  declared. Recommendation: declare **128-bit conjectured** (the standard
  plonky3-ecosystem position — the same conjecture the Poseidon2 capacity
  bound already leans on) and take the −23%.
- **lb=4 grid points** buy more (−41%) but charge the prover ~3–6x on the
  dominant commit phase. Per-turn proving is on the turn critical path;
  not worth it today.

The 186→159 base-column compaction (the filed lane): 27 columns off a
1,654-column extended row is **~1.6% of the opening proof, ≈ 7 KiB**. Worth
having as hygiene, irrelevant to proof economics. The real width lever is
the four Poseidon2 hash-site aux blocks — 1,408 of the 1,654 columns (85%).
Any future trace-shape work that moves permutation aux out of row-width
(e.g. a dedicated hash table via the batch prover's multi-table support, or
fewer/merged hash sites) dwarfs both the column compaction and the query
knob combined.

## 3. The transport story (who needs which proof)

- **Turn counterparties / the node admission gate / the browser verifier**
  receive the per-turn 451.7 KiB proof and verify it natively in ~22 ms
  (WASM in-browser runs the same verifier a small constant factor slower).
  This artifact travels one hop (prover → counterparty/node) and is then
  *consumed*: it never needs to be re-shipped to history audiences. 452 KiB
  for a one-hop, 22 ms-verifiable attestation is unremarkable; if it must
  shrink, §2's query knob is the lever.
- **A light client / a bridge** receives the whole-chain ROOT: 46.4 KiB +
  ~2 KiB binding proof + four public field elements, against a 32 B
  out-of-band anchor, verifying in 2 ms regardless of K. *This* is the
  artifact whose size answers "the proof is big" for external consumers —
  and it is already small.
- **The honest caveat on the ROOT, named:** the recursion config
  (`create_recursion_config`, `plonky3_recursion_impl.rs:254` — consumed by
  `ivc_turn_chain`, `joint_turn_recursive`, and the descriptor-leaf wrap)
  runs FRI with **num_queries=2, pow=0 → ≈6 bits conjectured FRI
  soundness**. The 46.4 KiB
  root is real machinery at demo-strength parameters. Production-strength
  (≥128-bit conj at lb=3) needs ~38–43 queries: the root grows roughly
  linearly in queries (≈ 15 KiB fixed + ~16 KiB/query ⇒ ~600–700 KiB), the
  in-circuit FRI verifier grows ~20x (it re-verifies every query of every
  wrapped child), and fold times grow accordingly — OR the fork gains
  grinding/cap-height options to claw that back. Raising the recursion
  config (and re-measuring the fold) is the single highest-value
  proof-economics lane open; until then the ROOT must not be presented as a
  production light-client artifact.

## 4. The Pickles wrap (interop lane): what exists, what was built, the distance

### What `stark_in_pickles` verifies today

`circuit/src/backends/stark_in_pickles.rs` wraps a **`PoseidonStarkProof`**
— the bespoke in-house STARK engine (`poseidon_stark.rs`), re-proven with
Poseidon-over-Pasta-Fp Merkle commitments so Kimchi's *native* Poseidon gate
(~12 rows/hash) can walk the paths in-circuit. Three honest boundaries:

1. **One AIR shape.** The in-circuit constraint-evaluation section is
   hardcoded to `MerkleStarkAir` (width 6, degree 4) —
   `poseidon_stark_verifier_circuit.rs:779-797`. It verifies no p3 proof of
   any kind, and not the EffectVM descriptor statement.
2. **1 query by default.** `WrapConfig::default()` re-checks one FRI query
   in-circuit; measured: the minimal wrap circuit is **643 Kimchi rows** and
   the resulting pickles step proof is **4.6 KiB** (composed: 4.8 KiB),
   wrap+verify a couple of seconds. The full 80-query circuit estimates
   ~50.6K rows and needs a 2¹⁶ Kimchi domain (over the original 2¹⁵ design
   target).
3. **The pickles step does not verify the Kimchi proof in-circuit.** The
   recursive step (`backends/mina/pickles.rs::prove_recursive_step`) proves
   a small hash-transition circuit with an IPA accumulator carried forward
   (assisted recursion); the 30K-row Kimchi STARK-verifier proof is
   self-checked host-side at wrap time and then **dropped** —
   `PicklesWrappedStark` carries only the step proof. An external verifier
   of the wrapped artifact checks the hash-chain step, not STARK validity:
   anyone who computes the two blake3 hashes can produce an identical
   artifact without ever constructing the Kimchi proof. As a *soundness*
   artifact for external consumers the wrap is therefore currently vacuous;
   it is interop scaffolding.

### Can the IVC ROOT be wrapped? The measured obstruction

The ROOT is a `BatchStarkProof` whose Merkle commitments are
**Poseidon2-width-16-over-BabyBear**. BabyBear *values* embed natively in
Pasta Fp (the field is not the obstruction); the **hash** is: Kimchi has no
Poseidon2-BabyBear gate, so every commitment-path step must be re-executed in
emulated BabyBear arithmetic.

The unit cost is measured for real, not estimated:
`backends/poseidon2_bb_kimchi.rs` arithmetizes one width-16
Poseidon2-BabyBear permutation in Kimchi Generic gates (eager modular
reduction, full copy-constraint wiring, witness differentially checked
against the native `crate::poseidon2`, proven and verified with the real
Kimchi prover over Vesta):

| | value |
|---|---|
| rows per permutation (eager reduction) | **5,908** |
| mul gadgets / add gadgets | 772 / 1,192 (3 rows each, + 16 constant pins) |
| end-to-end build+prove+verify | 2.6 s (domain 2¹³) |
| tampered-witness refusal | exercised (`tampered_witness_refused`) |

The K=2 ROOT's structural census: **420 Merkle digests + 9,827 field
elements** ⇒ ≈ 420 compressions + ≈1,230 sponge absorptions ≈ **~1,650
Poseidon2-BabyBear permutations** to re-verify the root's commitment openings
and Fiat–Shamir replay — *at today's 2-query demo config*. At
5,908 rows each that is ≈ **9.7 million Generic rows**, i.e.
~**150x** the largest practical Kimchi domain (2¹⁶ = 65,536), before
counting the Fiat–Shamir challenger replay or FRI-fold extension-field
arithmetic. Lazy reduction (reduce only
before S-boxes) cuts roughly 3x; it does not change the conclusion. At a
production-strength 40-query root the count multiplies by ~20 again.

So the full-hog "pickles-wrap the root" is **genuinely obstructed**, and the
obstruction is precisely localized: it is not the field, not the proof
format per se, but the **commitment hash at the final layer**. The distance,
in order:

1. **(fork)** Instantiate the *final* recursion layer's MMCS with a
   Pasta-Poseidon hash (the same boundary-layer hash-switch
   `poseidon_stark.rs` performs for the bespoke engine, and the same trick
   RISC0/SP1 use for their terminal SNARK wraps). The fork's MMCS is
   generic over the hasher; the work is a second `StarkConfig` + transcript
   for the last `build_and_prove_aggregation_layer` call only.
2. **(circuit)** A Kimchi verifier circuit for the *batch*-STARK shape
   (multi-table, LogUp, preprocessed commitments) — with step 1 its Merkle
   paths become native Poseidon rows again (~12/hash), putting it in the
   same ~30–60K row class as the existing bespoke-shape circuit.
3. **(pickles)** Real in-circuit composition: today's assisted-recursion
   step cannot attest "a Kimchi proof verified"; closing boundary 3 above
   means an in-circuit Kimchi verifier (true Pickles step/wrap machinery),
   which this lane does not have and o1's OCaml stack does.

### Verdict

**Keep-as-interop; do not invest now; do not retire.** The measured numbers
say the system's real proof-size answer for external verifiers is already
the BabyBear ROOT — 46.4 KiB / 2 ms / K-independent — once the recursion
config is production-strength; that config (q=2→~40, plus fold-time
re-measurement) is where proof-economics investment actually belongs, and it
is fork-config work, not Pickles work. The Pickles lane's honest state is:
a real native-hash Kimchi STARK verifier for the bespoke engine (643 rows at
1 query, ~50.6K estimated at full 80 — valuable as the §4-distance step-2
template), a pickles step whose
composition is currently hash-binding rather than in-circuit verification
(boundary 3 — must be closed before any "Mina-style O(1)" claim), and a now-
measured bridge cost (5,908 rows/permutation, ~150x over the largest
domain) that rules out brute-force wrapping. Retire nothing: `poseidon_stark`
+ the verifier circuit embody exactly the hash-switch pattern step 1 needs.
Revisit with funding only if Mina-ecosystem verification becomes a product
requirement.
