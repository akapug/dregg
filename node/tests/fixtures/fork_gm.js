// fork_gm.js — a private server that INSTANCES its world via deos.server.fork().
//
// The deos-host runs this on the persistent SpiderMonkey thread, attached to the node's
// live ledger as the server (GM) agent. The host has substituted the player's cell hex
// for "__PLAYER__" below. The program's setup:
//   1. forks a party/session INSTANCE — a fresh OPEN, funded cell minted on the live
//      ledger (a real verified turn through the host);
//   2. ADMITS the player to the instance — a GM superpower grant of a capability over the
//      instance cell to the player (a real GrantCapability turn), so the player's signed
//      cross-cell write into the instance is authorized (the executor's reach gate); and
//   3. registers a cap-gated "raise-flag" affordance SCOPED to the instance (the
//      `instance` field), carrying a real SetField on the instance cell itself.
//
// The cap tooth on the affordance (`required: signature`) is the gate the player must
// satisfy to DISCOVER + fire it; the granted instance cap is what lets the fire's effect
// REACH the instance cell. The host publishes the instance as its OWN discoverable surface
// (keyed by the instance cell), so a client connects to THAT party/session and fires in.

// (1) GM superpower: fork a party instance (a real mint). Returns the instance cell hex.
var instance = deos.server.fork("party-session-1");

// (2) GM superpower: admit the player into the instance (grant a cap over it). The grant's
//     `required` is None so the player's no-extra-proof signed write authorizes.
deos.server.grant("__PLAYER__", instance, "none");

// (3) Register the cap-gated "raise-flag" affordance SCOPED to the instance:
//     fire ⇒ SetField(instance, slot 0 := 1).
deos.server.defineAffordance({
    name: "raise-flag",
    required: "signature",
    instance: instance,
    effects: [
        { type: "setField", cell: instance, index: 0, value: 1 }
    ]
});

// Witness: 1 iff the instance forked (a 64-char hex id).
(instance && instance.length === 64) ? 1 : 0;
