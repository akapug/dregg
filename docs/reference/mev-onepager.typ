// One-pager: MEV in fee-recycling flywheels, measured — and the fix proven over
// all adversaries. Single portrait page, screenshot-ready as one tweetable image.
// Compile: typst compile --format png --ppi 135 mev-onepager.typ mev-onepager.png

#let accent = rgb("#175e54")     // proof teal
#let hazard = rgb("#a33b2e")     // the leak
#let inkdim = luma(92)
#let ink    = luma(24)
#let sans   = "Helvetica Neue"

#set page(width: 170mm, height: auto, margin: (top: 0mm, bottom: 7mm, x: 11mm))
#set text(font: "Libertinus Serif", size: 8.6pt, fill: ink)
#set par(justify: true, leading: 0.52em, spacing: 0.75em)

#show raw: set text(font: "DejaVu Sans Mono")
#show raw.where(block: false): set text(size: 7.6pt, fill: accent.darken(30%))
#show raw.where(block: true): it => block(
  fill: luma(249),
  stroke: (left: 1.3pt + accent.lighten(40%), rest: 0.4pt + luma(228)),
  inset: (x: 2.6mm, y: 1.7mm),
  width: 100%,
  radius: 1.5pt,
  text(size: 7.0pt, it),
)

#show heading.where(level: 1): it => block(above: 2.6mm, below: 1.6mm,
  stack(spacing: 1.1mm,
    text(font: sans, size: 11.5pt, weight: "bold", fill: accent.darken(10%), it.body),
    line(length: 100%, stroke: 0.8pt + accent.lighten(40%))))

#set list(marker: text(fill: accent, "▸"), indent: 0.8mm, body-indent: 1.6mm, spacing: 0.5em)

// ── Masthead — full-bleed ink ───────────────────────────────────────────────
#block(width: 100% + 22mm, inset: (x: 11mm, top: 7.5mm, bottom: 5.5mm), outset: 0mm,
  fill: luma(16), move(dx: -11mm)[
  #text(font: sans, size: 20.5pt, weight: "bold", fill: white)[The Sandwich in the Flywheel]
  #v(1.6mm)
  #text(font: sans, size: 10.3pt, fill: luma(200))[
    MEV in fee-recycling mechanisms, *measured* — and a fix *proven over all adversaries*
  ]
  #v(1.8mm)
  #text(font: sans, size: 7.2pt, fill: luma(150))[
    applied cryptography · a technical explainer about a *pattern*, not any particular project · dregg, 2026-07
  ]
])
#v(2.6mm)

// ── Lede ────────────────────────────────────────────────────────────────────
#text(size: 9.3pt)[
  A common on-chain tokenomics pattern — the *fee-recycling flywheel* — routes protocol
  fees back into the token: fees accrue → the protocol *market-buys* its own token on an
  AMM → the proceeds are added as locked liquidity. The loop is easy to build and easy to
  narrate. It is also easy to *sandwich*: the recycle buy is scheduled, public, and priced
  by pool state, so a bot buys just before it (pushing the price up), lets the mechanism
  buy at the worse price, and sells just after — extracting value from the flywheel and
  the holders it was built to reward.
]
#v(1.2mm)

// ── The two flows ───────────────────────────────────────────────────────────
#let node(body, tint: luma(247), edge: luma(200)) = box(
  fill: tint, stroke: 0.5pt + edge, radius: 1.5pt, inset: (x: 1.5mm, y: 1.2mm),
  text(font: sans, size: 6.5pt, body))
#let arr = text(fill: luma(140), size: 8pt, sym.arrow.r)
#grid(columns: (1fr, 1fr), column-gutter: 5mm,
  block(width: 100%, stroke: 0.5pt + hazard.lighten(45%), radius: 2pt, inset: 2.4mm, {
    text(font: sans, size: 7.4pt, weight: "bold", fill: hazard)[THE LEAKY LOOP]
    v(1.4mm)
    box({node[fees]; arr; node(tint: hazard.lighten(88%), edge: hazard.lighten(50%))[*market buy* on AMM]; arr; node[LP add]})
    v(1.2mm)
    text(font: sans, size: 6.6pt, fill: hazard.darken(10%))[
      ▴ bot front-runs the buy · mechanism fills at the pushed price · bot back-runs
    ]
  }),
  block(width: 100%, stroke: 0.5pt + accent.lighten(40%), radius: 2pt, inset: 2.4mm, {
    text(font: sans, size: 7.4pt, weight: "bold", fill: accent)[THE SEALED LOOP]
    v(1.4mm)
    box({node[fees]; arr; node[split #box(text(style: "italic")[ρ])]; arr; node(tint: accent.lighten(86%), edge: accent.lighten(40%))[*sealed batch* \@ #box(text(style: "italic")[p\*])]; arr; node[pool]})
    v(1.2mm)
    text(font: sans, size: 6.6pt, fill: accent.darken(8%))[
      ▴ one uniform clearing price, order-invariant — there is no swap to wrap
    ]
  }),
)
#v(1.6mm)

// ── Stat row ────────────────────────────────────────────────────────────────
#let stat(num, cap, tone: ink) = block(width: 100%, fill: luma(248),
  stroke: (top: 1.4pt + tone, rest: 0.4pt + luma(228)), radius: 1.5pt,
  inset: (x: 1.8mm, y: 1.7mm), {
    text(font: sans, size: 13.5pt, weight: "bold", fill: tone, num)
    v(0.9mm)
    text(font: sans, size: 6.4pt, fill: inkdim, cap)
  })
#grid(columns: (1fr, 1fr, 1fr, 1fr), column-gutter: 2.6mm,
  stat[#text(fill: hazard)[1.781 ETH]][sandwiched out of ONE 20 ETH recycle buy (measured, real bot)],
  stat[#text(fill: hazard)[\~16.6%]][fewer tokens for the *last* buyer vs the *first* — order is an input],
  stat[#text(fill: accent)[0 wei]][MEV on the sealed clearing, same harness — and a theorem says why],
  stat[16–28×][gas premium of the sealed path — real, bounded, named below],
)
#v(0.6mm)

// ── Two columns: measured / proven ──────────────────────────────────────────
#grid(columns: (1fr, 1.18fr), column-gutter: 6mm,
[
= The leak, measured

An adversarial A/B harness (`forge`, local) runs two real contracts on identical
token infrastructure: the sealed flywheel vs a *faithful mock of the common
pattern* — owner-settable split, market buy against a constant-product AMM, LP
add. Not a strawman: it prices exactly like a standard pump-style pool.

A real `SandwichBot` front-runs a *20 ETH* recycle with 5 ETH and back-runs it,
extracting *1,781,027,284,951,285,741 wei ≈ 1.781 ETH* — about *8.9%* of the
recycle — from the mechanism and its holders. The same pool shows the ordering
edge directly: two identical 5 ETH buyers in opposite order, and the first
receives *\~16.6% more* tokens than the last. These numbers scale with
trade-size-to-liquidity — pool-specific, not universal. What *is* structural is
the sign: market-buy recycle *> 0*, sealed recycle *= 0*.

The mock also has no conservation statement — the 1.781 ETH just *leaves*, with
nothing on-chain to notice. And a test where the sandwich fails is still only a
test: *one* bot failed on *one* input.
],
[
= The fix, proven

Replace the market buy with a *sealed-bid uniform-price clearing*: asks are
committed, then revealed, then the batch clears at *one* price #box(text(style: "italic")[p\*]) for
everyone. The clearing price is a function of the *book*, not of transaction
order — so position buys nothing. Measured on the same harness: *0 wei* MEV.
And the zero is not "our bot lost" — it is a theorem, quantified over *all*
adversaries (`metatheory/Market/RecycleFlywheel.lean`, Lean 4):

```
recycle_reorder_invariant :
  ANY permutation of the book clears at the
  SAME uniform price, IDENTICAL per-asset
  netFlow — order is not an input.
recycle_insertion_futile :
  ANY adversary leg admitted to the clearing
  nets ZERO surplus, by
  uniform_price_no_arbitrage — at one price
  every feasible trade is a fair swap.
split_enforced :
  a recycle deviating from the committed
  ρ·fee is UNCONSTRUCTABLE, not audited.
recycle_conserves :
  split + clearing + pool pairing net to
  zero; the pool stays solvent.
```

All `sorry`-free and axiom-clean (`#assert_all_clean` over the twenty flywheel
keystones), with worked non-vacuity witnesses both ways: a concrete sandwich
reorder that *fires and yields nothing*, and a concrete 60/40 skim against the
committed 50/50 that is *refused*.
],
)

// ── Costs band ──────────────────────────────────────────────────────────────
#block(width: 100%, fill: luma(247), stroke: (left: 1.6pt + luma(120), rest: 0.4pt + luma(225)),
  radius: 1.5pt, inset: (x: 3mm, y: 2.2mm), {
  text(font: sans, size: 8.6pt, weight: "bold", fill: luma(40))[What it costs — named, not footnoted]
  v(1.1mm)
  set text(size: 8.0pt)
  list(
    [*Gas + latency.* The sealed finalize step runs *\~1.62M gas* vs *\~96k* for the
     market buy (\~16–19× on the step; *\~28×* across the whole commit→reveal→clear→settle
     turn, plus a real commit→reveal wait). Bounded, under optimization — and the honest
     price of the guarantees above. The sealed path is *not* cheaper or faster.],
    [*Open weld — price binding.* The on-chain proof does *not* yet bind the clearing
     price inside its public statement. Mitigated, not closed: the price is *replayable*
     from the public sealed book, so a corrupt operator can *withhold* (→ timeout-refund)
     but cannot *misprice*. Closing it means carrying the clearing tuple into the proof.],
    [*Open weld — model ↔ `.sol`.* The theorems govern a Lean model; the correspondence
     to the deployed Solidity is source-reading, un-mechanized. No differential test yet
     pins one to the other.],
  )
  v(0.6mm)
  text(size: 7.4pt, fill: inkdim)[
    Both welds are *graded in the proof itself*: `welds_named_not_proved` machine-checks
    that neither is claimed as a ∀-adversary theorem. And a fairly-recycled worthless
    token is still worthless — this neutralizes mechanism abuse, not token quality.
  ]
})
#v(1.4mm)

// ── Moral ───────────────────────────────────────────────────────────────────
#block(width: 100%, fill: accent.darken(35%), radius: 2pt, inset: (x: 3.2mm, y: 2.4mm), {
  text(font: sans, size: 10.5pt, weight: "bold", fill: white)[Verify, don't trust.]
  h(2.4mm)
  text(size: 8.6pt, fill: luma(225))[
    A green test that a sandwich *failed* is not a proof that no sandwich *can* — and
    value visibly accruing is not value provably conserved. Visible ≠ verified: make the
    front-run *unconstructable*, then pay — and state — the real cost of doing so.
  ]
})
#v(0.8mm)
#text(size: 6.6pt, fill: inkdim, font: sans)[
  Sources (dregg repo): measured A/B `docs/reference/RECYCLE-FLYWHEEL-MEASURED.md`
  (harness `chain/test/RecycleFlywheelAB.t.sol`, 9/9 adversarial tests, suite 268/268) ·
  proofs `metatheory/Market/RecycleFlywheel.lean` over `Market/{Priced,Optimality,Liquidity}.lean`.
  No specific project is named or implied — the leaky loop is a *pattern*, and the point is the fix.
]
