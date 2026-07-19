# Output-Boundary MPC — the No-Viewer Crossing PoC

*Codex Round-4's highest-value construction, now built through a process-shaped
party-thread runtime at semi-honest PoC scope. It targets a
Tier-0 "no viewer" **cryptographic threshold bound**, and
**dissolves the BFV→TFHE scheme-switch seam** the fold-envelope flagged as the
crux. What-is, present tense; every edge names its grade; the honest threshold
caveat is stated, not buried. The PoC is real and cited (§7).*

Sources this refines: `FHEGG-CODEX-ROUND4.md` (the headline reframe + the
threshold-trust correction), `fhegg-fhe/ADDITIVE-FOLD-ENVELOPE.md` (the measured
additive fold + the named un-measured scheme-switch seam), `MEASURED-ENVELOPE.md`
(the exact-integer TFHE baseline), `DREGGFI-PRIVACY-TIERS.md` +
`DREX-NO-VIEWER-SURPASS.md` (the Tier-0 claims this note corrects).

---

## 0. Five-line summary

1. **The crossing's nonlinearity is irreducible; paying for it inside TFHE is
   not.** `p*` is deliberately public, so the comparison need not run under FHE at
   all. Keep the aggregate curve under the exact RLWE/BFV fold; at the OUTPUT
   BOUNDARY the `n` parties collectively decrypt a one-time-padded aggregate,
   derive additive shares locally, and run the crossing in MPC, revealing only
   `p*` + `V*`.
2. **This dissolves the scheme-switch seam architecturally.** Mask + collective
   BFV decrypt + local re-sharing needs no CHIMERA/PEGASUS BFV→TFHE adapter. The
   algebraic boundary, n-of-n BFV custody, party-owned arithmetic ingress, and
   boolean-MPC party runtime are built and composed in-process. Authenticated
   isolated-process deployment is not yet one production protocol.
3. **The implemented key custody is n-of-n, not t-of-n.** The Rust threshold API
   gives each party an opaque BFV secret share and refuses an `n−1` combine. It is
   now party-shaped and wire-framed, but the tests still run locally and do not
   establish authenticated distributed or malicious security.
4. **The sign vector stays shared.** The circuit computes every per-bucket minimum
   and a balanced, lowest-index-stable argmax under sharing, then opens only
   `(p*,V*)`. The sign-flip shortcut is not equivalent to this volume-argmax rule.
5. **The honest caveat.** All `n` BFV parties together can decrypt, and their key
   shares are reusable. "Nobody ever, even if all collude" is impossible for
   clearing over hidden data. **Grade: the algebra, n-of-n BFV threshold path,
   party-owned mod-t ingress, direct-peer A2B, and party-thread crossing are built
   and tested; an authenticated malicious no-viewer protocol remains §8's frontier.**

---

## 1. The problem this solves

`ADDITIVE-FOLD-ENVELOPE.md` measured the Tier-0 lever: swapping the exact-integer
TFHE fold for a carry-free additive BFV fold makes the aggregation **~10⁵× cheaper
and sub-10 ms**, recovering the kernel's "aggregation is the cheap part" thesis.
But it left two facts standing:

- **The crossing cannot be additive.** `sign`/`min`/`first-crossing` are not affine
  over the ciphertext ring; no additive scheme does the comparison. The crossing
  stays on TFHE (measured ~12–17 s, O(K), N-independent) — *or* it moves.
- **The BFV→TFHE scheme-switch is a named, un-measured seam.** To feed the
  BFV-folded curves into a TFHE comparator without decrypting them, a deployment
  needs a BFV→LWE/TFHE switch (CHIMERA ePrint 2018/758, PEGASUS 2020/1606). No
  clean Rust implementation exists; it is the one real residual of the fold path.

Output-boundary MPC removes *both*: the comparison leaves FHE entirely (no TFHE
crossing to pay for, no scheme-switch to build), and lands in a secret-shared MPC
whose only revealed output is `(p*, V*)`.

---

## 2. The construction

### (a) The additive RLWE/BFV fold (already built, measured)

Each trader locally expands its order into a **unary K-bucket increment vector** (a
bid of limit `L` puts its qty on buckets `0..=L`; an ask on `L..K`), SIMD-packs it
into ONE BFV ciphertext, and submits it. The server folds the N submissions into
two aggregate curve ciphertexts by native carry-free `+=`:

`Enc(D[p]) = Σ_bids inc[p]`,  `Enc(S[p]) = Σ_asks inc[p]`  — O(N) carry-free adds.

This is `fhegg-fhe/src/additive.rs::bfv_fold`, measured at 0.0003–0.0054 s for
N∈{32,512} (`ADDITIVE-FOLD-ENVELOPE.md`). `D` is non-increasing, `S`
non-decreasing (from the unary encoding). The limit `L` never leaves the trader;
the server only ever sums ciphertexts.

### (b) The output-boundary MPC crossing

The target `n` parties hold shares of the collective BFV key. At the boundary
they add secret random masks under BFV, collectively decrypt only the padded
value `y = D[p] + Σr_i (mod t)`, then locally derive additive shares whose sum is
`D[p]`; likewise for `S[p]`. Section §7.5 pins that algebra. `threshold.rs` pins
the n-of-n BFV operations, while `mpc_party.rs` takes each party's local mod-t
rows directly, peer-distributes fresh boolean shares, performs exact A2B/mod-t
reduction, and executes the crossing without sending input rows to the coordinator.

They then run the crossing in a secret-shared MPC:

1. **Per-bucket volumes.** Securely compute `v[p] = min(D[p],S[p])`; the comparison
   bits and minima remain shared.
2. **`p*`.** Run a balanced secure argmax tournament over `v`, selecting the lower
   index on equality. Only the winning index is opened.
3. **`V*`.** Open the winning shared minimum — never the sign vector, the losing
   minima, or either curve height individually.

The public transcript is `{batch root, p*, V*}` plus the one-time-pad-masked MPC
messages. A receipt for the current rule must prove that `V* = min(D[p*],S[p*])`,
that every bucket's executable volume is at most `V*`, and that no lower index
ties it. The older pair of crossing-boundary inequalities proves a different
largest-crossing rule and does **not** certify the volume argmax (the named
counter-witness has its volume peak away from that boundary). Binding this exact
max-selection relation to the committed aggregate remains a proof-layer
obligation; this MPC circuit alone is the untrusted finder.

### (c) Why the sign vector is not opened

An earlier shortcut proposed opening `c[p] = [D[p] ≥ S[p]]`. The current rule is
instead `argmax_p min(D[p],S[p])`: its lowest volume maximizer need not equal the
sign-vector flip index, so opening `c` is neither required nor justified as a
function of the published result. The current circuit keeps every comparison bit
shared, performs the balanced argmax with secret MUXes, and opens only `(p*,V*)`.
Section §7B pins the actual three-field transcript; there is no sign-vector
leakage argument in the current protocol.

---

## 3. The target security model — and what the PoC establishes

**Target adversary.** A coalition `C ⊂ {1..n}` of parties, `|C| < t`, plus the
public transcript (batch root, ciphertexts, proof, and `(p*,V*)`). The deployed
Rust threshold construction currently has `t=n`; it is not a general t-of-n scheme.

**Desired guarantee.** The joint view of `C` — its key shares, its
additive shares of every curve coefficient, and every MPC message — is
*computationally independent of every individual order and of every curve
coefficient*, conditioned on the public output `(p*, V*)`. Concretely:

- Any `n−1` additive shares of a value are uniform and independent of it (the
  sharing is information-theoretically hiding below `n` parties).
- Every message opened in the online phase is a **one-time-pad-masked bit** (`x ⊕
  a`, `a` a fresh uniform Beaver-triple bit), so the message stream is uniform and
  input-independent.
- The only non-masked opened values are `p*` and `V*` — the intended public output.

For the online MPC circuit, fresh Beaver masks give the usual semi-honest
simulation argument. Section §7B implements a schedule/correspondence simulator;
`mpc_party.rs` additionally runs the protocol in distinct party threads and
strictly checks the distributed public transcript schema. It still does not model
authenticated network transport, maliciously corrupted processes, or the complete
computational-security hybrid from BFV through MPC. Therefore the repository does
not yet prove that an adversarial coalition learns exactly `(p*,V*)` and nothing else.

**Reusable-key caveat.** BFV collective keygen avoids constructing one master
secret key, but the parties retain reusable secret shares. All `n` cooperating
parties can produce decrypt shares for any compatible ciphertext; selecting only
aggregate ciphertexts is a protocol/API obligation, not an impossibility theorem.
Output-boundary MPC narrows the intended reveal to `(p*,V*)`; it does not erase
the custody risk of long-lived threshold-FHE shares.

**What integrity requires (stated separately).** Both the one-process circuit and
party-thread runtime assume semi-honest execution. A malicious party can push a
wrong `p*`/`V*` — eventually caught by
the STARK boundary check (the comparator is outside the soundness TCB). Malicious
*privacy* (a party deviating to learn more) needs the maliciously-secure online
phase of §8; the semi-honest bound is what the PoC establishes.

### The honest caveat (no overclaim, no undersell)

- The additive/Beaver masks give a real semi-honest algebraic privacy argument,
  and the checked artifact now includes party-owned input/triple state plus
  channel-routed execution. In-memory unauthenticated channels are not a
  distributed adversarial theorem.
- It is currently **n-of-n**: all `n` parties can combine shares and see the
  curve (and could partial-decrypt orders). "Nobody even if
  all collude" is **impossible** for clearing over hidden data — the clearing is a
  function of the orders, so *someone* able to compute it can, in coalition,
  recompute its inputs' aggregate. Output-boundary MPC does not claim to escape
  that. The intended protocol narrows the normal reveal to `(p*,V*)`; hardening
  that intention against malicious parties is named work.

---

## 4. What the seam dissolution buys (vs. the pure-FHE crossing)

| | Pure-FHE crossing (`ADDITIVE-FOLD-ENVELOPE.md`) | Output-boundary MPC (this note) |
|---|---|---|
| Comparison carrier | TFHE `ge`+select, O(K) | secret-shared Beaver-triple `≥`, O(K·b) gates, O(b log K) modeled depth |
| Measured crossing cost | ~12–17 s (CPU) | historical pre-tournament CPU run: ~1–7 ms; rebench required (§7C) |
| BFV→TFHE scheme-switch | **needed, un-measured seam** | **none** — masked collective BFV decrypt + local re-sharing + party-thread MPC ingress are composed |
| Who can see a coefficient | nobody (stays encrypted); committee holds reusable key shares | fewer than `n` cannot combine the current BFV shares; all `n` hold a reusable decryption capability |
| Latency driver | PBS throughput (FPGA target) | modeled opening depth = `(max(b,2)+1)(1+⌈log₂K⌉)` |
| Online liveness | 1 threshold decrypt of `p*` | all `n` parties online in the current threshold and MPC paths; `n−1` is refused |

The target adds an **online multi-party MPC dependency** for one clearing — which the
public-`p*`, threshold-decrypt posture already implies. In exchange the presumed
crossing bottleneck AND the scheme-switch both disappear.

---

## 5. Candidate party set: the federation (infrastructure reuse, not crypto reuse)

The natural deployment candidate is the **federation nodes**, but today's
federation threshold module is not the BFV scheme used here:

- `federation/src/threshold_decrypt.rs` Shamir-shares a symmetric AEAD key over
  GF(256). It can inform membership, messaging, and operational ceremony, but it
  cannot decrypt BFV ciphertexts or supply BFV/GMW shares.
- `fhegg-fhe/src/threshold.rs` is the actual collective-BFV path. It is n-of-n and
  now exposes opaque party state plus framed public key/decrypt-share messages.
  Threshold conversion to `t<n` would require a different protocol, not a config
  change to the federation AEAD stack.
- Output-boundary MPC would **add a different cryptographic layer**: today `trustless.rs` is threshold-
  *decrypt* (the committee sees the book after batch close — `DREX-NO-VIEWER-
  SURPASS.md` rung 3 names this exactly). The MPC crossing makes it threshold-
  *compute*: the parties compute the clearing on shares and open only `(p*, V*)`,
  so no party ever sees the book. This is the rung-3→"no single viewer" jump the
  ladder flagged as real work. Only the party/transport scaffolding is plausibly reusable.

The additive shares of the curve coefficients are a re-sharing at the boundary.
The current party-thread Beaver phase runs among the selected BFV/MPC parties over
direct in-memory channels; authenticated external transport remains deployment work.

---

## 6. The concrete MPC choice — secret-sharing + Beaver-triple comparison

**Chosen: boolean (GF(2)) additive secret sharing + a GMW/Beaver-triple secure
comparator**, over a garbled circuit. The justification:

- **The circuit is comparison-shaped.** The crossing is K mutually independent secure
  minima followed by a balanced `K`-way argmax tournament. A `≥` is a ~3`b`-AND
  bit ripple. The exact gate ledger is
  `K·4b + (K−1)·(4b+⌈log₂K⌉)`: 8,506 ANDs at K=64 and 34,744 at K=256
  for `b=16`. This is still in the cheap regime for secret-sharing MPC.
- **Multi-party by default.** The federation is `n=3–5` parties, not 2. GMW/SPDZ-
  style secret sharing is natively n-party; garbled circuits are cleanest for 2
  parties and need extra machinery (BMR) for n>2. The party set decides the tool.
- **The online phase is information-theoretically secure given the masked
  openings.** Given Beaver triples (offline/preprocessing), each dependency layer
  of independent ANDs can share one batched opening; XOR is free. The K secure
  minima batch by circuit depth; the
  balanced argmax then has `⌈log₂K⌉` levels whose nodes batch independently.
  The exact modeled depth is `(max(b,2)+1)(1+⌈log₂K⌉)`: 119 rounds at
  `(b=16,K=64)` and 153 at K=256, rather than the sequential scan's thousands.
- **The masked opens are one-time pads**, which makes the public-transcript
  argument (§3) clean: the recorded message stream is uniform, so the transcript
  simulator is direct and the circuit opens only `(p*,V*)` by construction.
- **Reveal-only-`V*` for the volume.** All per-bucket minima remain shared through
  the tournament; only the winning min opens, never either curve height.

Garbled circuits would be a reasonable alternative for a **2-party** boundary
(e.g., a solver ⊕ a single custody node); for the n-party federation, secret
sharing is the fit. The preprocessing (Beaver triples) is the SPDZ offline phase:
in the PoC a simulated dealer produces them; in production they come from OT/HE
preprocessing among the parties (§8) — the online phase carries the security.

---

## 7. The PoC — real MPC, measured (cited run)

`fhegg-fhe/src/mpc.rs` (the circuit oracle), `src/mpc_party.rs` (party runtime),
and `src/bin/mpc_bench.rs` (the historical harness). Real
GF(2) secret sharing, real Beaver-triple AND gates (one-time-pad opens), a real
bit-sliced secure `≥`, a balanced secure argmax, and a real secure `min`. The
The legacy one-process harness receives clear curves to create its simulated
shares. The party runtime does not: each `PartyArithmeticInput` receives only one
party's mod-t rows, and the triple dealer receives public session shape only.
Only `(p*,V*)` are recorded as unmasked circuit openings. Reproduce the historical
harness with `cargo run --release --bin fhe-mpc-bench` from
`fhegg-fhe/`. The captured CPU run below predates the balanced-tournament
cutover. Its correctness witnesses remain regression tests, but its wall times
are retained only as historical baselines; rerun the harness before citing
current timings. The numeric `Transcript::rounds` column and the corrected
harness footer report the authoritative modeled circuit-depth ledger.

### (A) Correctness — MPC `(p*,V*)` == the plaintext crossing, over REAL BFV curves

The current exact circuit ledger at `b=16` is:

| K | secure-min + tournament ANDs/triples | modeled opening depth |
|---:|---:|---:|
| 64 | 8,506 | 119 |
| 256 | 34,744 | 153 |

The unit regression spans power-of-two and non-power-of-two shapes through K=256,
checks every result against `reference_clear`, and carries explicit adversarial
tie witnesses across odd tournament brackets.

### (B) Privacy schedule — reveal only `(p*,V*)`

The current `Transcript` has exactly three message classes:

- `masked`: `d=x⊕a` and `e=y⊕b` Beaver openings, each one-time-padded by a
  fresh uniform triple bit;
- `revealed_pstar`: the winning index bits;
- `revealed_vstar`: the winning volume bits.

There is no opened sign vector and no opened per-bucket minimum. The balanced
tournament's pair/carry schedule, AND count, masked-opening count, and modeled
depth depend only on public `(K,b)`. The regression runs different secret curves
at the same shape and checks all four schedule quantities are equal; it also
checks that `simulate`, given only the public result and `(K,b)`, produces the
same gate/opening/depth ledger. Distributional simulation follows directly from
the fresh uniform Beaver masks. The party runtime adds strict per-session ordering,
full-quorum refusal, and channel-level transcript teeth; these do not claim
authenticated or maliciously secure transport.

### (B2) Party-owned mod-t ingress and execution

`fhegg-fhe/src/mpc_party.rs` removes the clear-curve dealer from the online path:

- each party constructs an opaque `PartyArithmeticInput` from only its own demand
  and supply mod-t rows (the output shape of `MaskedBoundaryParty`);
- that party independently XOR-shares every bit to its peers over direct channels;
  the coordinator has no peer-channel endpoint and never receives an input row;
- each coefficient's source shares are summed in an actual balanced adder tree,
  with public odd carries, then reduced mod `t` by `n−1` oblivious conditional
  subtractions before entering the unchanged balanced crossing;
- the trusted triple dealer remains explicit, but its API accepts only the public
  session shape. It cannot be passed aggregate curves or party input rows;
- the coordinator requires all `n` gate and output messages, rejects cross-session,
  duplicate, malformed, and non-canonical messages, and reconstructs only
  `(p*,V*)`.

The truncation from the exact mod-t result to the declared output width relies on
the upstream fold/wrap-bound promise that every reconstructed curve coefficient is
`< 2^b`. The semi-honest circuit does not secretly range-check malicious inputs;
that validity condition remains explicit rather than being smuggled into the claim.
The composed integration passes real `MaskedBoundaryParty`-derived rows into this
runtime and pins `n−1` refusal, odd/non-power-of-two tournaments, lowest-index ties,
session/shape rejection, and the reveal-only schema.

### (C) Latency — logarithmic tournament depth

The captured pre-tournament one-process run was **0.9–7 ms**, versus the
**~12–17 s** TFHE O(K) crossing it replaced (`ADDITIVE-FOLD-ENVELOPE.md`). That
CPU timing is not yet a post-cutover benchmark. The load-bearing network ledger
is an exact, tested circuit-depth model for the crossing: **119 batched opening
layers for K=64 and 153 for K=256 at b=16**. This is `O(b log K)`, not the false
K-independent 48-layer claim, and not the sequential argmax formerly implemented.
The current party runtime executes scalar gate openings and reports that physical
count separately. Its strict modeled depth includes the implemented balanced A2B
tree, `n−1` mod-t reductions, and crossing; it does not mislabel modeled batching
as measured network behavior.

**Honest PoC scope.** (i) `mpc.rs` remains a one-process oracle/harness;
`mpc_party.rs` uses distinct party threads but still one host and unauthenticated
in-memory channels. (ii) Beaver triples come from a trusted offline dealer (SPDZ
offline phase); its new API sees only public shape, and the online phase is real
given those triples. (iii) the boundary integration now passes party-local mod-t
rows into the distributed A2B/crossing runtime; it does not establish isolated
process custody or an authenticated wire protocol. (iv) semi-honest circuit
reasoning only; malicious-secure online execution is §8.

### §7.5 MASKED DECRYPT-TO-SHARES — the decrypt-into-shares step, made real (measured)

The one modelled step above — "sharing the true committed coefficients" — is now a
real protocol (`fhegg-fhe/src/boundary.rs` + `fhe-boundary-bench`), and it dissolves
the missing primitive the same way §4 dissolved the scheme-switch: **mask, THEN
decrypt.** Each party homomorphically adds an encrypted uniform `Z_t` mask to the
folded curve ciphertext (`ct' = ct ⊞ Enc(r_0) ⊞ … ⊞ Enc(r_{n-1})` — n more
carry-free adds); the decryption then opens ONLY `y = (m + Σr_i) mod t`, an **exact
one-time pad** (enumeration-proven over the full mask space, even against a
coalition knowing all-but-one mask — `pad_is_exact_and_secret_independent`); each
party derives its mod-t share LOCALLY (`σ_0 = y − r_0`, `σ_i = −r_i`); one
`a2b_mod_t` bridge (exact secret-shared sum + n−1 oblivious conditional
subtractions of the public `t`) feeds the UNCHANGED crossing.

> **⚠ CORRECTED 2026-07-17 — this section used to claim "production needs no new partial-decrypt primitive
> at all — the EXISTING federation threshold-decrypt is pointed at `ct'`, because its output is now safe to
> open." That is a CATEGORY ERROR and it would not compile, let alone hold.**
> `federation/src/threshold_decrypt.rs` is a **symmetric** scheme — Shamir-shared *symmetric* key +
> BLAKE3-keyed **ChaCha20-Poly1305 AEAD** — and it says so itself (`:9-14`: *"This is a prototype scheme
> optimized for simplicity… At epoch start, a **dealer** generates a random 32-byte symmetric key"*). You
> cannot point an AEAD decryptor at a **BFV ciphertext**; `ct'` needs a *BFV threshold partial-decrypt*,
> which is a different primitive entirely. Two unrelated things share the name "threshold decrypt" — a
> false cognate, and the sort this repo has been deleting.
> **What masking DOES buy (real, measured below):** the opened value is `y = x + r`, so whoever performs the
> decrypt learns nothing about `x`. **What it does NOT buy:** custody of the BFV *secret key*. If one party
> holds `sk`, it can decrypt the UNMASKED aggregate directly and the no-viewer property is gone — masking
> the output does not fix key custody at the input.
> **The real primitive, and it is closer than the old claim pretended:** `fhe.rs 0.1.1` (ALREADY in the
> lockfile) ships `mbfv` (Mouchet et al., ePrint 2020/304) — collective keygen (`PublicKeyShare` +
> `CommonRandomPoly`) and collective decryption (`DecryptionShare`). **Verified caveats, upstream:** n-of-n
> only (no t-of-n), and the smudging noise is a literal upstream `TODO`
> (`mbfv/secret_key_switch.rs:76`: *"TODO this should be exponential in ciphertext noise!"*) — so the
> IND-CPA-D noise channel named at `boundary.rs:54-57` is open UPSTREAM too, not just here.
> `NoViewerKeyCustodyResidual` — NAMED, not claimed.

Measured (M2 Max, real BFV + real MPC, every row exactly equal to the plaintext
reference; `AGG→p*` = mask + decrypt + a2b + crossing — the R4 decisive metric):

| N | K | n | fold | mask | decrypt | a2b | crossing | **AGG→p\*** |
|---|---|---|---|---|---|---|---|---|
| 32 | 64 | 3 | 0.3 ms | 4.6 ms | 1.0 ms | 9.8 ms | 1.9 ms | **17.4 ms** |
| 128 | 64 | 4 | 1.4 ms | 6.4 ms | 1.0 ms | 13.5 ms | 2.1 ms | **23.1 ms** |
| 512 | 64 | 3 | 5.8 ms | 5.1 ms | 1.1 ms | 8.8 ms | 2.0 ms | **16.9 ms** |
| 128 | 256 | 4 | 1.4 ms | 6.5 ms | 1.0 ms | 59.4 ms | 8.7 ms | **75.6 ms** |

The PoC measures the full **one-process value computation**: fold (carry-free BFV)
→ masked opening (one-time pad) → mod-t shares → a2b → Beaver crossing →
`(p*,V*)`, in tens of milliseconds after order encryption. The historical boundary
harness decrypts `ct'` in-process. The newer party-shaped path composes real n-of-n
BFV keygen, independently retained masks, framed encrypted-mask contributions, and
smudged threshold decrypt shares without constructing a joint secret key
(`threshold_masked_boundary_channels`). Its channels and party threads are a custody/API
tooth, not authenticated transport. That same integration now passes the locally
derived rows into `mpc_party.rs`: parties peer-share them, run distributed exact
A2B/mod-t reduction, and complete the crossing without a clear-curve input dealer.
The symmetric federation decryptor cannot be used for this step.

---

## 8. The named frontier (honest residuals)

- **Threshold-BFV boundary deployment.** `boundary.rs` now composes §7.5's exact
  mask/decrypt/re-share algebra with `threshold.rs`'s real n-of-n BFV collective
  keygen and smudged decrypt shares. The channel integration keeps both threshold
  shares and masks in party-owned state, carries only strict framed public messages,
  refuses `n−1`, mixed-ciphertext shares, and even a self-consistent full quorum for
  the wrong ciphertext, and never constructs a joint secret key. Its local rows now
  feed the party-thread MPC runtime. What remains is
  authenticated isolated-process transport, malicious-share validity, persistent
  zeroized custody, and replay/crash recovery. Moving to
  `t<n` is a protocol change. **Grade: process-shaped composition built and KAT'd;
  adversarial distributed deployment named.**
- **Malicious security.** The PoC online phase is semi-honest. Malicious security
  (a deviating party cannot learn more than `(p*,V*)` nor force an undetected wrong
  result beyond what the STARK catches) needs authenticated shares (SPDZ MACs) +
  verifiable partial decryption + transcript-level smudging composition. The
  symmetric federation module's MAC framing may inspire transport engineering,
  but it is not a malicious-security proof or BFV share authenticator.
- **Real preprocessing.** Beaver triples from OT/HE preprocessing among the parties
  (MASCOT/Overdrive), not a dealer. Standard; offline; off the latency path.
- **STARK boundary binding.** The current rule needs a proof that
  `V*=min(D[p*],S[p*])`, every bucket's volume is at most `V*`, and no lower index
  ties it. The older adjacent crossing inequalities certify a different rule and
  are insufficient. Instantiating the exact volume-argmax/tie relation against the
  committed aggregate is named work; the MPC remains an untrusted finder.

None of these overturn the construction; they sharpen the PoC toward deployment on
the labelled trajectory. What is real today is the n-of-n collective-BFV algebra,
the exact mask/decrypt/share identities, the one-process circuit oracle, and a
party-thread runtime from local mod-t rows through A2B and crossing. An adversarial
no-viewer deployment still needs isolated party processes, authenticated
transport, malicious-protocol hardening, and the scalar-smudging-to-full-transcript
hybrid correspondence; it is not a measured production property of this PoC.

---

## 9. The claim, stated exactly

> **Tier-0's no-viewer is the target; this PoC establishes its algebraic spine.**
> The aggregate demand/supply curve is folded under exact RLWE/BFV. The current
> n-of-n threshold module computes smudged partial decryptions, and the current
> secret-shared circuit computes `p* = argmax_j min(D[j],S[j])` while opening only
> `(p*,V*)`. Tests pin both against the plaintext and fhe.rs oracles. The party
> runtime accepts only party-local mod-t rows, peer-shares them, and composes with
> the masked-boundary integration. Today those parties are hosted as threads in
> one process, triple preprocessing is trusted, transport is unauthenticated, and the full
> transcript-security bridge is conditional. Thus the code does not yet justify
> an adversarial distributed no-viewer headline. It does eliminate the need for a
> BFV→TFHE scheme switch: the intended boundary is masked collective BFV
> decryption, local re-sharing, then the MPC comparison.

---

## 10. See also

- `fhegg-fhe/src/mpc.rs` — the protocol (secret sharing, Beaver-triple `≥`,
  crossing, `min`, simulator).
- `fhegg-fhe/src/mpc_party.rs` — party-owned mod-t ingress, direct-peer boolean
  sharing, exact A2B/mod-t reduction, full-quorum Beaver routing, and crossing.
- `fhegg-fhe/tests/threshold_masked_boundary_channels.rs` — the composed
  threshold-mask → local rows → party MPC integration tooth.
- `fhegg-fhe/src/bin/mpc_bench.rs` — the cited PoC harness.
- `fhegg-fhe/ADDITIVE-FOLD-ENVELOPE.md` — the additive fold + the (now dissolved)
  scheme-switch seam.
- `fhegg-fhe/src/additive.rs` — the real BFV fold this composes with.
- `federation/src/threshold_decrypt.rs`, `intent/src/trustless.rs` — the distinct
  symmetric threshold stack whose membership/transport scaffolding may be reused,
  but whose cryptography cannot process BFV.
- `docs/deos/FHEGG-CODEX-ROUND4.md` §Q1.3.4 — the reframe + the threshold-trust
  correction this note builds.
- `docs/deos/DREGGFI-PRIVACY-TIERS.md`, `docs/deos/DREX-NO-VIEWER-SURPASS.md` — the
  Tier-0 claims corrected to the adversarial-threshold posture.
