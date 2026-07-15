// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// ============================================================================
// RECONSTRUCTED ACCESS-CONTROL-BUG SAMPLE — NOT a real project, audit-target only.
//
// This token is a deliberate demonstration of the MISSING-ACCESS-CHECK door that
// INV-ACCESS-CONTROL catches and INV-CAP alone does NOT. It is HARD-CAPPED and
// ONE-SHOT (so the supply-cap invariant `totalSupply <= cap` genuinely holds — the
// auto-harness proves INV-CAP), but its `mint` FORGOT the `msg.sender == minter`
// guard. So ANY caller — not just the designated `minter` — can fire the one-shot
// mint and capture the ENTIRE disclosed supply to their own wallet. The cap is
// respected; the AUTHORITY is not.
//
// The point: a grep for `minter`/`onlyMinter` sees the `minter` field and could
// wrongly conclude the mint is role-gated. Only the symbolic access-control proof
// (INV-ACCESS-CONTROL) reveals the door — a counterexample where `caller != minter`
// successfully moves the supply. This is the contrast case in
// docs/deos/CONTRACT-VERIFIER-IMPROVEMENTS.md: two invariants catch two doors.
// ============================================================================

contract UnguardedMintToken {
    string public name = "Unguarded";
    string public symbol = "UNG";
    uint8 public constant decimals = 18;

    uint256 public immutable cap; // real, enforced hard cap
    uint256 public totalSupply;
    address public minter; // the INTENDED authorized minter (set to deployer)
    bool public minted; // one-shot latch (so INV-CAP holds)

    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    constructor(uint256 cap_) {
        require(cap_ != 0, "zero cap");
        cap = cap_;
        minter = msg.sender;
    }

    // THE ACCESS-CONTROL DOOR — cap + one-shot latch are enforced (so the hard cap
    // holds and INV-CAP passes), but there is NO `require(msg.sender == minter)`.
    // Any caller can be the one to fire the mint and take the whole disclosed supply.
    function mint(address to, uint256 amount) external {
        require(!minted, "already minted");
        require(amount <= cap, "cap exceeded");
        minted = true;
        totalSupply = amount;
        balanceOf[to] += amount;
        emit Transfer(address(0), to, amount);
    }

    function transfer(address to, uint256 value) external returns (bool) {
        _transfer(msg.sender, to, value);
        return true;
    }

    function transferFrom(address from, address to, uint256 value) external returns (bool) {
        allowance[from][msg.sender] -= value;
        _transfer(from, to, value);
        return true;
    }

    function approve(address spender, uint256 value) external returns (bool) {
        allowance[msg.sender][spender] = value;
        emit Approval(msg.sender, spender, value);
        return true;
    }

    function _transfer(address from, address to, uint256 value) internal {
        require(balanceOf[from] >= value, "insufficient");
        balanceOf[from] -= value;
        balanceOf[to] += value;
        emit Transfer(from, to, value);
    }
}
