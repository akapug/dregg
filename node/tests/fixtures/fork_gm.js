// fork_gm.js — a private server that INSTANCES its world via deos.server.fork().
//
// The deos-host runs this on the persistent SpiderMonkey thread, attached to the node's
// live ledger as the server (GM) agent. The program's setup:
//   1. forks a party/session INSTANCE — a fresh OPEN, funded cell minted on the live
//      ledger (a real verified turn through the host); and
//   2. registers a cap-gated "raise-flag" affordance SCOPED to that instance (the
//      `instance` field), carrying a real SetField on the instance cell itself.
//
// Because the instance is minted OPEN (set_state == None), a player's signed cross-cell
// SetField into it authorizes without a separate grant — the cap tooth on the affordance
// (`required: signature`) is the gate the player must satisfy. The host publishes the
// instance as its OWN discoverable surface (keyed by the instance cell), so a client
// connects to THAT party/session and fires into it.

// (1) GM superpower: fork a party instance (a real mint). Returns the instance cell hex.
var instance = deos.server.fork("party-session-1");

// (2) Register the cap-gated "raise-flag" affordance SCOPED to the instance:
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
