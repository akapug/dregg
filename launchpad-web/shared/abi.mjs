// abi.mjs — the DreggLaunchpad + DreggLaunchToken ABI the product layer drives.
//
// These fragments mirror EXACTLY the deployed engine at
//   chain/contracts/launchpad/DreggLaunchpad.sol
//   chain/contracts/launchpad/DreggLaunchToken.sol
// There is NO mirror of the mechanism here — the frontend/backend only read and
// call the real contract. The seal preimage is computed by calling the on-chain
// `sealOf` view (drift-free: the same keccak(abi.encode(price,qty,salt,bidder))
// the contract checks in revealBid), never re-derived in JS.

// Phase enum (DreggLaunchpad.Phase)
export const PHASE = ['None', 'Commit', 'Reveal', 'Cleared', 'Finalized'];

// Human-readable ABI (ethers v6 parses these directly).
export const LAUNCHPAD_ABI = [
  // ── registration ──
  'function registerLaunch(string tokenName, string tokenSymbol, (uint256 totalSupply,uint256 saleSupply,uint256 creatorAllocation,uint64 creatorLockUntil,uint256 reservePrice) s, uint64 commitDuration, uint64 revealDuration, address gate, address attestor) returns (uint256 launchId)',
  'function checkSchedule(uint256 launchId, (uint256 totalSupply,uint256 saleSupply,uint256 creatorAllocation,uint64 creatorLockUntil,uint256 reservePrice) s) view returns (bool)',
  // ── sealed commit → reveal ──
  'function commitBid(uint256 launchId, bytes32 sealedHash, bytes proof) payable',
  'function revealBid(uint256 launchId, uint256 price, uint256 qty, bytes32 salt)',
  'function sealOf(uint256 price, uint256 qty, bytes32 salt, address bidder) pure returns (bytes32)',
  // ── uniform-price clearing ──
  'function finalizeClearing(uint256 launchId, uint256[] order, bytes clearingProof)',
  // ── non-custodial settlement ──
  'function settleBid(uint256 launchId, address bidder)',
  'function withdrawProceeds(uint256 launchId)',
  'function claimCreatorAllocation(uint256 launchId)',
  // ── views ──
  'function launchCount() view returns (uint256)',
  'function TOKEN_UNIT() view returns (uint256)',
  'function phaseOf(uint256 launchId) view returns (uint8)',
  'function clearingPriceOf(uint256 launchId) view returns (uint256)',
  'function soldQtyOf(uint256 launchId) view returns (uint256)',
  'function tokenOf(uint256 launchId) view returns (address)',
  'function scheduleCommitOf(uint256 launchId) view returns (bytes32)',
  'function clearingAttested(uint256 launchId) view returns (bool)',
  'function revealedCount(uint256 launchId) view returns (uint256)',
  'function getBid(uint256 launchId, address bidder) view returns (bool committed, bool revealed, uint256 price, uint256 qty, uint256 filled, bool settled, uint256 deposit)',
  // ── events ──
  'event LaunchRegistered(uint256 indexed launchId, address indexed creator, address token, bytes32 scheduleCommit, uint64 commitEnd, uint64 revealEnd)',
  'event BidCommitted(uint256 indexed launchId, address indexed bidder, bytes32 sealedHash, uint256 deposit)',
  'event BidRevealed(uint256 indexed launchId, address indexed bidder, uint256 price, uint256 qty)',
  'event Cleared(uint256 indexed launchId, uint256 clearingPrice, uint256 soldQty, bool attested)',
  'event BidSettled(uint256 indexed launchId, address indexed bidder, uint256 filled, uint256 paid, uint256 refunded)',
  'event ProceedsWithdrawn(uint256 indexed launchId, address indexed creator, uint256 amount)',
  'event CreatorAllocationClaimed(uint256 indexed launchId, address indexed creator, uint256 amount)',
];

export const TOKEN_ABI = [
  'function name() view returns (string)',
  'function symbol() view returns (string)',
  'function decimals() view returns (uint8)',
  'function totalSupply() view returns (uint256)',
  'function cap() view returns (uint256)',
  'function minted() view returns (bool)',
  'function balanceOf(address) view returns (uint256)',
  'event Transfer(address indexed from, address indexed to, uint256 value)',
];
