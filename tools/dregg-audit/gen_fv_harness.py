#!/usr/bin/env python3
"""Generate a Halmos symbolic harness for the ERC-20 supply-cap shape.

Usage: gen_fv_harness.py <contract.sol> <out_harness.sol>

Prints the detected shape to stdout ("token-cap" or "unknown"). Only the
supply-cap shape is auto-generated: a contract with a `mint` function plus a
public `cap` and public `totalSupply` (so `t.cap()` / `t.totalSupply()` getters
exist). Anything else returns "unknown" and the pipeline reports scaffold-only —
FV is deliberately NOT push-button for arbitrary contracts.

The harness proves INV-CAP (`totalSupply <= cap`) over any single external call and
over a two-mint sequence, all inputs symbolic, against the REAL compiled bytecode.
For a hard-capped one-shot token (e.g. DreggLaunchToken) Halmos proves it; for an
uncapped/owner-mintable token (e.g. the MoonRugToken sample) Halmos returns a
counterexample.

When the token exposes public `balanceOf`+`allowance` it also emits INV-NODRAIN
(owner-drain/seize, door #8) and INV-REENTRANCY (an ETH-conservation guard, the
auto best-effort form). When it exposes a public authority accessor (`minter` or
`owner`) it emits INV-ACCESS-CONTROL (door #1): the mint op is confined to that role
— a mint missing its access-check yields a counterexample even when the cap holds.
The deep both-polarity re-entry proof is the hand-written spec
chain/formal-verification/DreggReentrancyFV.t.sol; the strong access-control /
no-drain specs are its siblings there.
"""
import re
import sys

def strip_comments(s: str) -> str:
    s = re.sub(r"/\*.*?\*/", "", s, flags=re.S)
    s = re.sub(r"//[^\n]*", "", s)
    return s

def find_primary_contract(code: str):
    """Return (name, body-start-index) of the contract defining `function mint`."""
    contracts = list(re.finditer(r"\bcontract\s+([A-Za-z_]\w*)", code))
    for m in contracts:
        start = m.end()
        # crude: search the rest of the file for a mint fn belonging to this contract
        # (good enough — samples are single-contract or contract-then-helpers)
        seg = code[start:]
        nxt = re.search(r"\bcontract\s+[A-Za-z_]\w*", seg)
        body = seg[: nxt.start()] if nxt else seg
        if re.search(r"function\s+mint\b", body):
            return m.group(1), body
    if contracts:
        return contracts[0].group(1), code[contracts[0].end():]
    return None, ""

def parse_ctor_params(code: str, name: str):
    """Return list of (solidity_type, is_string) for the contract's constructor."""
    m = re.search(r"\bconstructor\s*\(", code)
    if not m:
        return []
    # balance parens
    i = m.end()
    depth = 1
    while i < len(code) and depth:
        if code[i] == "(":
            depth += 1
        elif code[i] == ")":
            depth -= 1
        i += 1
    inner = code[m.end(): i - 1].strip()
    if not inner:
        return []
    params = []
    for raw in split_top_commas(inner):
        raw = raw.strip()
        if not raw:
            continue
        toks = raw.split()
        typ = toks[0]
        is_string = typ.startswith("string") or typ.startswith("bytes") and typ == "bytes"
        params.append((typ, is_string))
    return params

def find_privileged_movers(body: str):
    """Return names of external/public functions with a `(address, address, uint256)`
    signature — the owner-drain / seize / rescue shape (taxonomy door #8).

    `transferFrom` is the ONE legitimate member of this shape (it is allowance-gated,
    which the INV-NODRAIN antecedent already excludes), so it is dropped. Any OTHER
    function of this shape is a candidate privileged balance-mover and is dispatched
    into the drain harness so Halmos decides whether it is an actual unauthorized
    drain (proof) rather than a grep name-match (heuristic)."""
    movers = []
    # Capture the header from `function NAME(...)` through the modifiers up to the
    # opening brace, so visibility can be checked. Only externally-callable
    # (external/public) movers are dispatchable; internal/private helpers like a
    # `_transfer(address,address,uint256)` are excluded.
    for m in re.finditer(
        r"function\s+([A-Za-z_]\w*)\s*\(\s*address\s+\w+\s*,\s*address\s+\w+\s*,\s*uint256\s+\w+\s*\)([^{;]*)[{;]",
        body,
    ):
        name, mods = m.group(1), m.group(2)
        if name == "transferFrom" or name in movers:
            continue
        if re.search(r"\b(external|public)\b", mods):
            movers.append(name)
    return movers

def split_top_commas(s: str):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur); cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return out

def main():
    src_path, out_path = sys.argv[1], sys.argv[2]
    raw = open(src_path).read()
    code = strip_comments(raw)
    name, body = find_primary_contract(code)

    has_mint = bool(name and re.search(r"function\s+mint\b", body))
    has_cap = bool(re.search(r"\bcap\b\s*[;=]", code) and re.search(r"public[^;]*\bcap\b", code))
    has_supply = bool(re.search(r"public[^;]*totalSupply|totalSupply[^;]*public", code))

    if not (has_mint and has_cap and has_supply):
        print("unknown")
        return

    # INV-NODRAIN (taxonomy door #8, owner-drain / seize) is generated when the
    # token exposes public `balanceOf` + `allowance` getters (so the antecedent
    # "caller holds no allowance over victim" and the balance readback compile).
    # Any detected privileged (address,address,uint256) mover is dispatched too, so
    # a seize/rescue door is decided by PROOF, not grep. This is best-effort on the
    # common owner-mintable shape; the strong path is the hand-written spec in
    # chain/formal-verification/ (DreggNoDrainFV.t.sol).
    has_balanceof = bool(re.search(r"public[^;]*\bbalanceOf\b|\bbalanceOf\b[^;]*public", code))
    has_allowance = bool(re.search(r"public[^;]*\ballowance\b|\ballowance\b[^;]*public", code))
    movers = find_privileged_movers(body)
    gen_drain = has_balanceof and has_allowance

    # INV-ACCESS-CONTROL (taxonomy door #1, owner/admin authority) is generated when
    # the token exposes a public authority accessor (`minter` or `owner`) so the
    # antecedent "caller is not the authorized role" and the readback compile. The
    # check proves the mint door is confined to that role — an UNGUARDED mint (a
    # missing access-check) yields a counterexample where a non-authority caller moves
    # the supply, even when the hard cap still holds (so INV-CAP alone would pass).
    has_minter = bool(re.search(r"public[^;]*\bminter\b|\bminter\b[^;]*public", code))
    has_owner = bool(re.search(r"public[^;]*\bowner\b|\bowner\b[^;]*public", code))
    auth_accessor = "minter" if has_minter else ("owner" if has_owner else None)
    gen_access = auth_accessor is not None

    params = parse_ctor_params(code, name)
    # Build symbolic ctor param decls + call args + assumes.
    decls, args, assumes = [], [], []
    ci = 0
    for typ, is_string in params:
        if is_string:
            args.append('"N"')
        else:
            pname = f"_c{ci}"; ci += 1
            decls.append(f"{typ} {pname}")
            args.append(pname)
            if typ.startswith("uint"):
                assumes.append(f"        vm.assume({pname} != 0 && {pname} < 1e30);")
    decl_str = (", ".join(decls) + ", ") if decls else ""
    args_str = ", ".join(args)
    assume_str = "\n".join(assumes)
    fname = src_path.split("/")[-1]

    # ── INV-NODRAIN harness (owner-drain / seize, taxonomy door #8) ──────────────
    drain_block = ""
    if gen_drain:
        # Dispatch the standard ERC-20 surface PLUS every detected privileged mover.
        mover_branches = "".join(
            f'        else if (k == {3 + i}) {{ vm.prank(caller); try t.{mv}(x, y, v) {{}} catch {{}} }}\n'
            for i, mv in enumerate(movers)
        )
        nbranch = 3 + len(movers)
        drain_block = f"""
    // Full external surface for the drain check: ERC-20 plus any detected
    // privileged (address,address,uint256) mover ({', '.join(movers) if movers else 'none detected'}).
    function _drainStep({name} t, uint8 sel, address caller, address x, address y, uint256 v) internal {{
        uint256 k = sel % {nbranch};
        if (k == 0) {{ vm.prank(caller); try t.transfer(x, v) {{}} catch {{}} }}
        else if (k == 1) {{ vm.prank(caller); try t.approve(x, v) {{}} catch {{}} }}
        else if (k == 2) {{ vm.prank(caller); try t.transferFrom(x, y, v) {{}} catch {{}} }}
{mover_branches}    }}

    // INV-NODRAIN: no caller who is neither the holder nor allowance-authorized can
    // reduce the holder's balance. PROVES the "owner-drain / seize" door absent on a
    // safe token; yields a COUNTEREXAMPLE on a privileged seize/drain door.
    function check_noUnauthorizedDrain({decl_str}address victim, uint256 seed, uint8 sel, address caller, address x, address y, uint256 v) public {{
{assume_str}
        {name} t = new {name}({args_str});
        // Best-effort victim seed via the disclosed mint door (owner/minter == this).
        try t.mint(victim, seed) {{}} catch {{}}
        vm.assume(caller != victim);
        vm.assume(t.allowance(victim, caller) == 0);
        uint256 b0 = t.balanceOf(victim);
        _drainStep(t, sel, caller, x, y, v);
        assert(t.balanceOf(victim) >= b0); // the no-drain tooth
    }}

    // INV-REENTRANCY (ETH-conservation form): the contract is seeded with ETH held
    // on others' behalf; NO single external call by an attacker over the dispatched
    // surface (ERC-20 + any privileged mover) may reduce that ETH. A pure ERC-20 has
    // no outbound value-call, so it is PROVEN drain-free; a payable value-sending
    // door yields a COUNTEREXAMPLE. This is the auto-harness's best-effort reentrancy
    // guard for the common token shape (single call, no callback carrier); the STRONG
    // both-polarity re-entry proof (CEI-violation vs CEI-correct, with a re-entrant
    // attacker) is the hand-written spec chain/formal-verification/DreggReentrancyFV.
    function check_noReentrancyDrain({decl_str}address attacker, uint8 sel, address x, address y, uint256 v) public {{
{assume_str}
        {name} t = new {name}({args_str});
        vm.deal(address(t), 1 ether); // the contract holds ETH on others' behalf
        uint256 e0 = address(t).balance;
        _drainStep(t, sel, attacker, x, y, v);
        assert(address(t).balance >= e0); // no external call drains the contract's ETH
    }}
"""

    # ── INV-ACCESS-CONTROL harness (owner/admin authority, taxonomy door #1) ──────
    access_block = ""
    if gen_access:
        access_block = f"""
    // INV-ACCESS-CONTROL: the privileged mint op is confined to the authorized role
    // (`{auth_accessor}`). For any caller that is NOT that role, the supply cannot
    // move — PROVEN on a correctly-gated mint; a COUNTEREXAMPLE on a mint missing its
    // access check (an unauthorized caller mints the supply), which INV-CAP alone
    // would miss when the cap+latch still hold. Grep sees the `{auth_accessor}` field
    // and assumes a guard; THIS proves the guard actually confines the op.
    function check_privilegedOpsAuthorized({decl_str}address caller, address to, uint256 amount) public {{
{assume_str}
        {name} t = new {name}({args_str});
        address auth = t.{auth_accessor}();
        vm.assume(caller != auth);
        uint256 s0 = t.totalSupply();
        vm.prank(caller);
        try t.mint(to, amount) {{}} catch {{}}
        assert(t.totalSupply() == s0); // no unauthorized caller moves the supply
    }}
"""

    harness = f"""// SPDX-License-Identifier: MIT
// AUTO-GENERATED by tools/dregg-audit/gen_fv_harness.py — do not edit by hand.
pragma solidity ^0.8.20;

import {{Test}} from "forge-std/Test.sol";
import {{{name}}} from "../target/{fname}";

/// Symbolic hard-cap proof (INV-CAP) for {name}, all inputs symbolic, against the
/// REAL compiled bytecode. EVM twin of the Lean supply theorem `execMintA_iff_spec`
/// (metatheory/Dregg2/Verify/KeystoneAuditSupply.lean:124).
contract GenFV is Test {{
    function _step({name} t, uint8 sel, address caller, address x, address y, uint256 v) internal {{
        uint256 k = sel % 4;
        if (k == 0) {{ vm.prank(caller); try t.mint(x, v) {{}} catch {{}} }}
        else if (k == 1) {{ vm.prank(caller); try t.transfer(x, v) {{}} catch {{}} }}
        else if (k == 2) {{ vm.prank(caller); try t.approve(x, v) {{}} catch {{}} }}
        else {{ vm.prank(caller); try t.transferFrom(x, y, v) {{}} catch {{}} }}
    }}

    // INV-CAP over ANY single external call.
    function check_cap_singleCall({decl_str}uint8 sel, address caller, address x, address y, uint256 v) public {{
{assume_str}
        {name} t = new {name}({args_str});
        _step(t, sel, caller, x, y, v);
        assert(t.totalSupply() <= t.cap());
    }}

    // INV-CAP over TWO arbitrary mint attempts (catches "second mint" / overdose).
    function check_cap_twoMints({decl_str}address c1, address to1, uint256 a1, address c2, address to2, uint256 a2) public {{
{assume_str}
        {name} t = new {name}({args_str});
        vm.prank(c1); try t.mint(to1, a1) {{}} catch {{}}
        assert(t.totalSupply() <= t.cap());
        vm.prank(c2); try t.mint(to2, a2) {{}} catch {{}}
        assert(t.totalSupply() <= t.cap());
    }}
{drain_block}{access_block}}}
"""
    open(out_path, "w").write(harness)
    print("token-cap")

if __name__ == "__main__":
    main()
