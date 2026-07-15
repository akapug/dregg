// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {DreggLaunchToken} from "contracts/launchpad/DreggLaunchToken.sol";

/// @title ACCESS-CONTROL-CORRECTNESS — SYMBOLIC formal verification (Halmos)
/// @notice A NEW anti-rug invariant, PROVEN not grepped: a privileged operation
///         (mint / pause / config / withdraw) is callable ONLY by its authorized
///         role — an unauthorized caller can NEVER change the privileged state. This
///         is the machine proof of the owner/admin door (#1 in the audit taxonomy,
///         `docs/deos/RUG-FORENSICS-VS-DREGG.md`): Stage-A grep only reports that an
///         `onlyOwner`/`minter` guard is PRESENT — it cannot tell a CORRECT guard
///         from a missing/mis-wired one. This proves the guard actually confines the
///         privileged op, over the full symbolic caller set, against the real
///         compiled bytecode.
///
/// THE INVARIANT (INV-ACCESS-CONTROL): for any caller that is NOT the authorized
/// role, any call to a privileged operation leaves the privileged state UNCHANGED
/// (equivalently: the call reverts). A contract satisfying it has no unauthorized
/// privileged-op door — the only way privileged state changes is an authorized
/// call. A contract with a missing/incorrect access-check admits a counterexample:
/// a non-authorized caller mutates the privileged state.
///
/// TWO POLARITIES (mirrors DreggNoDrainFV):
///   * SAFE   — `DreggLaunchToken.mint` (minter-only) and the inline `GuardedAdmin`
///     (owner-only setters) are PROVEN: no non-authorized caller can mint / change
///     config.
///   * UNSAFE — the inline `UnguardedAdmin` (a privileged setter with NO owner
///     check — the missing-`onlyOwner` bug) admits a COUNTEREXAMPLE: a non-owner
///     changes the privileged config. This is the door the audit must catch by
///     PROOF, not by a grep that would (wrongly) report the `owner` field as a
///     present-and-therefore-assumed-correct guard.
///
/// WHY HALMOS: identical to the sibling specs — the token's guard reverts with a
/// custom error (`NotMinter`), which solc CHC models as fall-through (spurious CEX).
/// Halmos runs the bytecode. See README §1.
///
/// BOUND: all inputs symbolic (authority, caller, args, ctor cap); call depth
/// bounded (single privileged call, and a 2-call sequence). Symbolic-bounded, like
/// the siblings.
contract DreggAccessControlFV is Test {
    // ── SAFE (real surface): only the minter can move DreggLaunchToken's supply ───
    // The access-control twin of the supply-authority biconditional: for any caller
    // that is not the constructor-designated `minter`, the mint door is closed — the
    // one-shot latch and totalSupply are untouched. PROVES the privileged mint op is
    // correctly role-gated over the full symbolic caller set.
    function check_launchToken_mintIsMinterOnly(
        uint256 cap,
        address minter,
        address caller,
        address to,
        uint256 amount
    ) public {
        vm.assume(cap != 0);
        vm.assume(caller != minter);
        DreggLaunchToken t = new DreggLaunchToken("N", "S", cap, minter);

        bool m0 = t.minted();
        uint256 s0 = t.totalSupply();
        vm.prank(caller);
        try t.mint(to, amount) {
            assert(false); // a non-minter must NEVER successfully mint
        } catch {
            // privileged state untouched by the unauthorized call
            assert(t.minted() == m0);
            assert(t.totalSupply() == s0);
        }
    }

    // ── SAFE (inline): a correctly-gated privileged op confines to the owner ──────
    // `GuardedAdmin.setConfig`/`setPaused` are `require(msg.sender == owner)`-gated.
    // For any non-owner caller, over any single privileged call, the config is
    // unchanged. PROVES the guard actually confines the op.
    function check_guardedAdmin_privilegedOpsAuthorized(
        address caller,
        uint8 sel,
        uint256 cfg,
        bool p
    ) public {
        GuardedAdmin g = new GuardedAdmin(); // owner == address(this)
        vm.assume(caller != g.owner());

        uint256 c0 = g.config();
        bool p0 = g.paused();
        _adminStep(g, sel, caller, cfg, p);
        // THE ACCESS-CONTROL TOOTH: a non-owner cannot change privileged state.
        assert(g.config() == c0);
        assert(g.paused() == p0);
    }

    // ── SAFE over a 2-call sequence (no two-step privileged escalation) ──────────
    function check_guardedAdmin_authorized_seq2(
        address c1, uint8 s1, uint256 cfg1, bool p1,
        address c2, uint8 s2, uint256 cfg2, bool p2
    ) public {
        GuardedAdmin g = new GuardedAdmin();
        vm.assume(c1 != g.owner() && c2 != g.owner());
        uint256 c0 = g.config();
        bool pp0 = g.paused();
        _adminStep(g, s1, c1, cfg1, p1);
        _adminStep(g, s2, c2, cfg2, p2);
        assert(g.config() == c0);
        assert(g.paused() == pp0);
    }

    // ── UNSAFE (inline): the missing-onlyOwner door is CAUGHT by counterexample ───
    // `UnguardedAdmin.setConfig` has NO owner check — the exact missing-access-check
    // bug. Halmos MUST find a non-owner caller that changes `config`, proving the
    // door is a real unauthorized-privileged-op (grep would see the `owner` field and
    // the `setPaused` guard and could wrongly assume the contract is access-gated).
    function check_unguardedAdmin_missingCheckIsCaught(
        address caller,
        uint256 cfg
    ) public {
        UnguardedAdmin u = new UnguardedAdmin(); // owner == address(this)
        vm.assume(caller != u.owner());

        uint256 c0 = u.config();
        vm.prank(caller);
        try u.setConfig(cfg) {} catch {}
        // EXPECTED: Counterexample — a non-owner changed the privileged config.
        assert(u.config() == c0);
    }

    // Dispatch the privileged-op surface: setConfig / setPaused, symbolic caller.
    function _adminStep(GuardedAdmin g, uint8 sel, address caller, uint256 cfg, bool p) internal {
        if (sel % 2 == 0) {
            vm.prank(caller);
            try g.setConfig(cfg) {} catch {}
        } else {
            vm.prank(caller);
            try g.setPaused(p) {} catch {}
        }
    }
}

// ─── Inline admin contracts (the access-control polarity pair; self-contained) ───

/// A correctly-gated privileged surface: every mutating op is `onlyOwner`. This is
/// the shape INV-ACCESS-CONTROL proves safe (no non-owner can change config/paused).
contract GuardedAdmin {
    address public owner;
    uint256 public config;
    bool public paused;

    constructor() {
        owner = msg.sender;
    }

    function setConfig(uint256 c) external {
        require(msg.sender == owner, "not owner");
        config = c;
    }

    function setPaused(bool p) external {
        require(msg.sender == owner, "not owner");
        paused = p;
    }
}

/// The missing-access-check bug: `setConfig` forgot its `onlyOwner` guard, so ANYONE
/// can change the privileged config (e.g. flip a fee, a router, an oracle). `owner`
/// and the `setPaused` guard exist — so a grep for `onlyOwner`/`owner` reports the
/// contract "has access control", masking the one unguarded door. Reconstructed,
/// self-contained, audit-target only. This is what INV-ACCESS-CONTROL must catch.
contract UnguardedAdmin {
    address public owner;
    uint256 public config;
    bool public paused;

    constructor() {
        owner = msg.sender;
    }

    // RUG DOOR — no owner check: any caller sets the privileged config.
    function setConfig(uint256 c) external {
        config = c;
    }

    function setPaused(bool p) external {
        require(msg.sender == owner, "not owner");
        paused = p;
    }
}
