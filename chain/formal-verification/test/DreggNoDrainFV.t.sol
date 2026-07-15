// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {DreggLaunchToken} from "contracts/launchpad/DreggLaunchToken.sol";

/// @title NO-PRIVILEGED-DRAIN — SYMBOLIC formal verification (Halmos)
/// @notice A NEW anti-rug invariant, PROVEN not grepped: no external call by a
///         caller who is neither the holder nor authorized by the holder can
///         REDUCE that holder's balance. This is the machine-proof twin of the
///         rug-forensics "owner-drain / seize" door (#5 in the taxonomy,
///         `docs/deos/RUG-FORENSICS-VS-DREGG.md` §1.2 HypervaultFi privileged
///         withdrawal), which the `dregg-audit` pipeline previously only detected
///         by GREP (Stage A PRESENT/ABSENT), never proved.
///
/// THE INVARIANT (INV-NODRAIN): for any holder `victim`, any single external
/// call by any `caller != victim` with `allowance(victim, caller) == 0` leaves
/// `balanceOf(victim)` non-decreasing. A contract that satisfies this has NO
/// privileged seize/drain door: the only ways a holder's balance can fall are
/// (a) the holder spends it themselves, or (b) a spender the holder explicitly
/// approved moves it — both excluded by the antecedent, so any drop is an
/// unauthorized drain.
///
/// WHY IT MATTERS: "owner-drain" is the single most damaging launchpad rug class
/// (HypervaultFi, and the `seize(from,to,value) onlyOwner` shape below). Grepping
/// for `seize|sweep|rescue|drain` finds the NAME; it cannot tell a benign
/// `rescue(stuck ERC-20)` from a `seize(any holder)` drain, and it misses a drain
/// spelled without those names. Proving INV-NODRAIN over the FULL external
/// surface, symbolically, against the REAL compiled bytecode decides it.
///
/// WHY HALMOS (not solc CHC): identical to the sibling specs — the guards use
/// custom errors (`revert InsufficientAllowance()`, `revert NotMinter(...)`),
/// which solc's CHC engine models as fall-through (spurious CEX). Halmos runs the
/// bytecode where a custom-error revert is a plain REVERT opcode. See README §1.
///
/// BOUND: all inputs symbolic (holder, caller, selector, amounts, ctor cap);
/// call depth bounded (single external call). Symbolic-bounded, like the siblings.
contract DreggNoDrainFV is Test {
    // Selector dispatch over the token's FULL external surface. `caller` symbolic
    // (vm.prank), args symbolic; a revert leaves state unchanged (try/catch).
    function _step(
        DreggLaunchToken t,
        uint8 sel,
        address caller,
        address a,
        address b,
        uint256 v
    ) internal {
        uint256 k = sel % 4;
        if (k == 0) {
            vm.prank(caller);
            try t.mint(a, v) {} catch {}
        } else if (k == 1) {
            vm.prank(caller);
            try t.transfer(a, v) {} catch {}
        } else if (k == 2) {
            vm.prank(caller);
            try t.approve(a, v) {} catch {}
        } else {
            vm.prank(caller);
            try t.transferFrom(a, b, v) {} catch {}
        }
    }

    // ── INV-NODRAIN — a SAFE token (DreggLaunchToken) has NO drain door ──────────
    // PROVES: over any single call on the full ERC-20 surface by an unauthorized
    // caller, the victim's balance never falls. DreggLaunchToken has no privileged
    // balance-mover, so this holds — the machine proof of "structurally no seize".
    function check_launchToken_noUnauthorizedDrain(
        uint256 cap,
        address minter,
        address victim,
        uint256 seed,
        uint8 sel,
        address caller,
        address a,
        address b,
        uint256 v
    ) public {
        vm.assume(cap != 0);
        vm.assume(seed <= cap);
        DreggLaunchToken t = new DreggLaunchToken("N", "S", cap, minter);

        // Give the victim a real balance via the ONE disclosed mint door.
        vm.prank(minter);
        try t.mint(victim, seed) {} catch {}

        // The antecedent: caller is not the victim and holds NO allowance over it.
        vm.assume(caller != victim);
        vm.assume(t.allowance(victim, caller) == 0);

        uint256 b0 = t.balanceOf(victim);
        _step(t, sel, caller, a, b, v);
        // THE NO-DRAIN TOOTH: an unauthorized caller cannot reduce victim's balance.
        assert(t.balanceOf(victim) >= b0);
    }

    // ── INV-NODRAIN over a 2-call sequence (no two-step drain on the safe token) ──
    function check_launchToken_noDrain_seq2(
        uint256 cap,
        address minter,
        address victim,
        uint256 seed,
        uint8 s1, address c1, address a1, address b1, uint256 v1,
        uint8 s2, address c2, address a2, address b2, uint256 v2
    ) public {
        vm.assume(cap != 0);
        vm.assume(seed <= cap);
        DreggLaunchToken t = new DreggLaunchToken("N", "S", cap, minter);
        vm.prank(minter);
        try t.mint(victim, seed) {} catch {}

        vm.assume(c1 != victim && c2 != victim);
        vm.assume(t.allowance(victim, c1) == 0);
        vm.assume(t.allowance(victim, c2) == 0);

        uint256 b0 = t.balanceOf(victim);
        _step(t, s1, c1, a1, b1, v1);
        _step(t, s2, c2, a2, b2, v2);
        assert(t.balanceOf(victim) >= b0);
    }

    // ── INV-NODRAIN — an UNSAFE token (privileged seize door) is CAUGHT ──────────
    // The negative control: `RuggableToken.seize(from,to,value) onlyOwner` is the
    // HypervaultFi owner-drain shape. Halmos must find a COUNTEREXAMPLE (the owner
    // seizes a non-consenting holder) — proving the invariant has teeth. Grep flags
    // the name `seize`; THIS proves it is an actual unauthorized drain.
    function check_ruggable_seizeIsAProvenDrain(
        address victim,
        uint256 seed,
        address caller,
        address to,
        uint256 v
    ) public {
        RuggableToken t = new RuggableToken(); // deployer == owner == address(this)
        vm.assume(victim != address(this));
        t.ownerMint(victim, seed); // owner seeds the victim's balance

        // Same antecedent as the safe proof: caller not the victim, no allowance.
        vm.assume(caller != victim);
        vm.assume(t.allowance(victim, caller) == 0);

        uint256 b0 = t.balanceOf(victim);
        // The full surface includes the privileged door. Halmos will choose
        // caller == owner, to == owner, v > 0 and drive balanceOf(victim) below b0.
        vm.prank(caller);
        try t.seize(victim, to, v) {} catch {}
        assert(t.balanceOf(victim) >= b0); // EXPECTED: Counterexample (drain found)
    }
}

/// A minimal reconstruction of the "owner-drain / seize" rug door (the same
/// mechanism as `tools/dregg-audit/samples/MoonRugToken.sol` §RUG DOOR #5, the
/// HypervaultFi privileged-withdrawal class). Inlined so this spec is
/// self-contained (the sample lives outside the FV project's `allow_paths`).
contract RuggableToken {
    address public owner;
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    constructor() {
        owner = msg.sender;
    }

    function ownerMint(address to, uint256 amount) external {
        require(msg.sender == owner, "not owner");
        totalSupply += amount;
        balanceOf[to] += amount;
    }

    function transfer(address to, uint256 value) external returns (bool) {
        balanceOf[msg.sender] -= value;
        balanceOf[to] += value;
        return true;
    }

    function approve(address spender, uint256 value) external returns (bool) {
        allowance[msg.sender][spender] = value;
        return true;
    }

    // RUG DOOR #5 — owner moves ANY holder's balance at will, no consent, no
    // allowance, no floor. This is what INV-NODRAIN must catch.
    function seize(address from, address to, uint256 value) external {
        require(msg.sender == owner, "not owner");
        balanceOf[from] -= value;
        balanceOf[to] += value;
    }
}
