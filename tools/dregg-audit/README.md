# `dregg-audit` — a repeatable DREGG-kernel contract-audit pipeline

Point it at any Solidity contract; it runs the same four-stage audit we ran ad-hoc
for our own launchpad this session, and produces a structured markdown report.

```sh
tools/dregg-audit/dregg-audit <contract.sol> [--out DIR] [--no-fv] [--no-codex] [--codex-timeout N]
```

**What it is:** an *assisted-audit tool*. It finds vulnerabilities and proposes
fixes, with a machine proof where a standard invariant applies. **It is not a
push-button certification** (a real audit needs human review), and it does **not**
auto-rewrite the contract to secure (that is a research problem — this AUDITS and
PROPOSES; a developer applies the fix). See `docs/deos/DREGG-AUDIT-SERVICE.md`.

## The four stages

| Stage | Tool | Decided by | Output |
|-------|------|-----------|--------|
| **A. rug-forensics** | `grep` over the rug-door taxonomy | **machine (deterministic)** | each door PRESENT/ABSENT (`docs/deos/RUG-FORENSICS-VS-DREGG.md`) |
| **B. formal verify** | Halmos symbolic EVM | **machine (proof)** | INV-CAP PROVEN / COUNTEREXAMPLE, or scaffold-only |
| **C. adversarial** | `codex exec` hostile audit | LLM (needs triage) | severity-ranked findings, **TRIAGE-REQUIRED** |
| **D. triage + report** | assembler | human confirms C | one markdown report |

- **A** scans for the nine documented rug doors (owner/admin role, mintable supply,
  proxy-upgrade, selfdestruct, honeypot transfer-gate, blacklist, pausable,
  owner-drain/seize, fee/tax manipulation). Deterministic — an ABSENT door is a
  structural absence in source; a PRESENT door is a *surface to review*.
- **B** auto-generates a Halmos harness for the ERC-20 **supply-cap** shape (a `mint`
  fn + public `cap`/`totalSupply`) and proves, over all inputs against the real
  compiled bytecode, up to **four invariant families** (each mapped to its taxonomy
  door in the report): **INV-CAP** (`totalSupply <= cap`, door #2 — the EVM twin of
  the Lean supply theorem `execMintA_iff_spec`); and, when the shape exposes the
  needed getters, **INV-NODRAIN** (door #8, owner-drain/seize — decided by proof,
  including any detected privileged `(address,address,uint256)` mover),
  **INV-REENTRANCY** (ETH-conservation form; the deep both-polarity re-entry proof
  is the hand-written `chain/formal-verification/DreggReentrancyFV.t.sol`), and
  **INV-ACCESS-CONTROL** (door #1 — a mint missing its role check yields a
  counterexample even when the cap holds). A hard-capped one-shot token *proves*;
  a rug-shaped token yields a *counterexample* on the door it opens. **Honest
  coverage:** that is proof on 3 of the 9 taxonomy doors (+ the reentrancy guard,
  which is outside the taxonomy); the other 6 doors (#3 proxy, #4 selfdestruct,
  #5 honeypot, #6 blacklist, #7 pause, #9 fee) are **grep-only, no proof** —
  extending harnesses toward them is a named next step. Non-token shapes report
  scaffold-only (FV is deliberately not push-button for arbitrary contracts —
  pool-solvency contracts use the hand-written harness in
  `chain/formal-verification/`).
- **C** runs `codex exec --sandbox read-only` with a hostile-auditor prompt covering
  every vuln class (`prompts/hostile-audit.txt`). codex errs both ways, so its
  findings are emitted **TRIAGE-REQUIRED** — a human confirms each against source.
- **D** assembles the report: the rug-door table (A, auto), the FV verdict (B, auto),
  the codex findings (C, triage-required), and a triage summary. A/B rows are
  machine-decided; C rows carry the codex severity and a proposed fix but require a
  human verdict (CONFIRMED-REAL / FALSE-POSITIVE / KNOWN-RESIDUAL).

## Layout

```
tools/dregg-audit/
  dregg-audit              # the orchestrator
  gen_fv_harness.py        # Stage-B harness generator (supply-cap shape)
  prompts/hostile-audit.txt# Stage-C codex prompt template
  samples/MoonRugToken.sol # a reconstructed known-rug sample (audit target)
  fv-workspace/            # Halmos foundry project (harness+target generated per run)
  reports/                 # generated audit reports (+ the committed sample run)
```

## The sample runs (committed evidence)

`reports/MoonRugToken.audit.md` + `.halmos.log` is a real run against
`samples/MoonRugToken.sol`, a reconstruction of publicly documented launchpad-token
rug mechanisms (SQUID honeypot, mintable-supply overdose, HypervaultFi owner-drain,
pausable/blacklist, selfdestruct). The pipeline flags 7 rug doors, and **Halmos
returns machine-checked counterexamples on three invariants** — INV-CAP twice (the
uncapped owner `mint`) and **INV-NODRAIN** (the owner-drain door, disproven by proof,
not just grep); INV-REENTRANCY and INV-ACCESS-CONTROL honestly PASS (the owner mint
*is* role-gated — each invariant closes its own door). This demonstrates the service
on a NON-DREGG contract.

`reports/UnguardedMintToken.audit.md` + `.halmos.log` is the **contrast case**
(`samples/UnguardedMintToken.sol`): a hard-capped one-shot token whose `mint` forgot
its `msg.sender == minter` guard. **INV-CAP PASSES** (the cap genuinely holds) while
**INV-ACCESS-CONTROL returns the counterexample** — any caller can fire the one-shot
mint and take the whole supply. A grep sees the `minter` field and could assume a
guard; only the symbolic proof reveals the door. Two invariants, two doors.

Reproduce:

```sh
tools/dregg-audit/dregg-audit tools/dregg-audit/samples/MoonRugToken.sol
tools/dregg-audit/dregg-audit tools/dregg-audit/samples/UnguardedMintToken.sol --no-codex
```

## Requirements

`halmos` (`uvx --from halmos halmos`, 0.3.3+), `forge`/`solc` (Foundry 1.7.1, solc
0.8.30), `codex` (codex-cli 0.144.1). Stages degrade gracefully: `--no-fv` /
`--no-codex` skip their stage, and a missing tool is reported, not fatal.
