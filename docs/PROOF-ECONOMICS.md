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
| whole-chain IVC ROOT (`WholeChainProof.root`, K=2) | postcard | **502.4 KiB** (514,489 B) | 30.7 s fold | **16 ms** | recursion config (lb=3, **q=38, pow=14** = 128-bit conjectured) |
| whole-chain IVC ROOT (K=3) | postcard | 502.4 KiB (514,498 B) | 44.5 s fold | 16 ms | same |
| + carried chain-binding proof (K=2 / K=3) | postcard | 18.8 / 28.4 KiB | — | included | same |
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

The ROOT proof is **K-independent**: K=2 and K=3 both serialize to 502.4 KiB
and verify in 16 ms. This is the genuine IVC property — the root's cost is the
root verifier-circuit's, not the history's. Fold time is what grows with K
(one leaf wrap + one aggregation layer per added turn, ~14 s each at this
config).

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
- **A light client / a bridge** receives the whole-chain ROOT: 502.4 KiB +
  a 19–29 KiB binding proof + four public field elements, against a 32 B
  out-of-band anchor, verifying in 16 ms regardless of K. *This* is the
  artifact whose size answers "the proof is big" for external consumers.
- **The ROOT's security config, named:** the recursion config
  (`create_recursion_config`, `plonky3_recursion_impl.rs` — consumed by
  `ivc_turn_chain`, `joint_turn_recursive`, and the descriptor-leaf wrap)
  runs FRI at **lb=3, num_queries=38, query-PoW=14 → 128 bits conjectured**
  (capacity-bound conjecture; ~71 bits proven/Johnson) — the same
  conjecture the per-turn production config stands on. Every proof in the
  recursion tree runs at this strength, and the in-circuit FRI verifier
  re-verifies all 38 queries plus the PoW witness of every wrapped child
  (`check_pow_witness` in the fork's circuit challenger). The measured cost
  of that strength: the root is 502.4 KiB (the in-circuit verifier's own
  FRI opening dominates, same shape as the per-turn artifact), folds run
  ~14 s per turn (30.7 s at K=2, 44.5 s at K=3, off the verification path),
  and root verification is 16 ms, K-independent. The remaining honest
  residuals on the ROOT are the fork follow-ups named in
  `circuit/src/ivc_turn_chain.rs` module docs (child-circuit identity
  pinning, public-value propagation) — config strength is no longer one of
  them.

## 4. The Pickles wrap: removed (the backends were unsound scaffolding)

The kimchi/pickles backend family is REMOVED from the tree:
`circuit/src/backends/{mina/, kimchi_native/, stark_in_pickles.rs,
poseidon2_bb_kimchi.rs}`, the bespoke `poseidon_stark.rs` engine +
`poseidon_stark_verifier_circuit.rs` it existed to feed, the `mina` cargo
feature, and the o1-labs git dependencies (kimchi / poly-commitment /
mina-curves / mina-poseidon / groupmap). The system's proof-size answer for
external verifiers is the BabyBear ROOT (§3): 502.4 KiB / 16 ms /
K-independent, at 128-bit-conjectured FRI.

Why removed rather than kept as an interop lane:

1. **The pickles step never verified the Kimchi proof in-circuit.** The
   recursive step proved a small hash-transition circuit with an IPA
   accumulator carried forward; the Kimchi STARK-verifier proof was
   self-checked host-side at wrap time and then dropped. An external
   verifier of the wrapped artifact checked a blake3 hash chain, not STARK
   validity — anyone could produce an identical artifact without ever
   constructing the Kimchi proof. As a soundness artifact the wrap was
   vacuous.
2. **The wrap covered the wrong statement.** The in-circuit
   constraint-evaluation section was hardcoded to one bespoke AIR shape
   (`MerkleStarkAir`, width 6) over the in-house `poseidon_stark` engine —
   never any Plonky3 proof, never the EffectVM descriptor statement the
   system actually proves.
3. **Brute-force wrapping the real ROOT is measured-infeasible on Kimchi.**
   One Poseidon2-BabyBear width-16 permutation costs 5,908 Kimchi Generic
   rows (measured, proven, tamper-checked); the K=2 ROOT needs ~1,650
   permutations ≈ 9.7 million rows, ~150x the largest practical Kimchi
   domain (2^16), before Fiat–Shamir replay or FRI-fold extension-field
   arithmetic. Lazy reduction cuts ~3x and does not change the conclusion.
4. **The kimchi_native circuits lacked copy constraints.** Generic gates
   wired every position to its own row and never threaded gadget outputs
   into dependent binding gates through the permutation argument, so a
   prover bypassing the honest `prove()` wrapper was unconstrained
   (the old AUDIT-circuit.md P0-2 finding). Production use was already
   forbidden.

What survives as knowledge: the measured numbers above, and the localized
shape of a future interop lane if Mina-ecosystem verification ever becomes a
product requirement — (1) a final recursion layer whose MMCS uses a
Pasta-native hash (the standard terminal-wrap hash-switch, as in RISC0/SP1
terminal SNARKs), (2) a Kimchi verifier circuit for the batch-STARK shape
(native Poseidon rows once step 1 lands), (3) real in-circuit step/wrap
machinery (which o1's OCaml stack has and this lane never did). Building
that would be a new, audited construction — not a revival of the removed
scaffolding.
