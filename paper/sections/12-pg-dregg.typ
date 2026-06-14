// =============================================================================
// Section 12: pg-dregg
// =============================================================================

#import "../defs.typ": lean
= pg-dregg: verified durable state <sec-pg>

The receipt chain of @sec-proofs is the truth and the database is a cache. pg-dregg
makes that relationship a concrete deployment: dregg as a PostgreSQL extension in
which *reads are ordinary SQL and writes are verified turns*. State exists in the
database only as the post-image of a turn the verified semantics accepted; an
application queries that state freely with `SELECT`, and every mutation passes
through the verifier. It is the embeddable realization --- the verified executor
of @sec-realization reachable from inside a database engine --- and it carries the
kernel's guarantees into a place applications already live.

== The spine invariant

The discipline is one sentence: state rows exist *only* as the post-image of a
verified turn, never by a bare SQL `INSERT`, `UPDATE`, or `DELETE`. Ordinary
`SELECT` reads the materialized state with no proof obligation, because reading
cannot violate a guarantee; writes are the only thing the verifier need gate, and
they are gated at the one door the schema exposes. The same capability token of
@sec-authority authorizes both sides --- a row-security policy that admits a read
and the credential a write must carry are the *same* decision, the verified
admission of @sec-authority --- so the database's access control and the kernel's
authority are not two systems kept in sync but one decision evaluated in two
places.

== The tiers

pg-dregg realizes the spine invariant in layers, each usable on its own and each
adding exactly one capability of the verified substrate to the database.

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*tier*], [*what it adds*]),
    [authorization], [dregg capabilities as row-security policies: a policy admits
      a row only when a configured-issuer credential authorizes the action,
      verified offline against the issuer key --- the @sec-authority admission
      decision, with no circuit and no network],
    [mirror], [the node tails its commit log into read-only tables (turns, cells,
      capabilities, memory); applications query verified state as plain SQL joins,
      and the sole writer is the verified commit path, so the spine invariant holds],
    [verified store], [the commit-log table is the only door to state, and a
      before-insert trigger re-validates the chain tooth --- turn $N$'s post-root is
      turn $N{+}1$'s pre-root, ordinals dense --- so a reordered, gapped, or
      substituted batch is refused by the database engine itself],
    [embeddable executor], [a database function executes a turn in-backend through
      the verified entry, producing the receipt and updating state in one
      transaction --- the database *is* the kernel, with turn and application data
      sharing one atomic commit],
  ),
  caption: [The pg-dregg tiers. Each is a point at which the verified substrate
    enters the database; the lower tiers are circuit-free and offline.],
)

The lower tiers are live and need no prover: the authorization tier is a credential
check compiled to a row-security predicate, and the mirror tier turns the database
into a query surface over verified state with the node as sole writer. The
verified-store tier's structural chain tooth --- the load-bearing per-row gate ---
is live and circuit-free; the database engine rejects a tampered commit batch
because the trigger re-runs the same chain re-validation the node does. The
range-based proof attestation that would attach a recursive-aggregation proof
(@sec-proofs) over a span of turns is designed and fails closed until its proof
serialization lands, so the tier never reports a range as attested that it has not
checked.

== The embeddable executor (Tier-D)

The deepest tier embeds the verified executor itself: a database function takes a
turn envelope and runs it in-backend through the compiled Lean entry of
@sec-realization, producing the receipt and the post-state in the same database
transaction as the application's own writes. The runtime it embeds is the
single-threaded, fork-safe configuration of the Lean runtime --- a private
allocator, lazy task management, a no-input-output initialization --- linked only
when the tier is enabled, so the default build never sees it. This is where the
kernel's theorems land directly in the data path: conservation, non-amplification
of delegated capabilities (#lean("Spec.gen_conferral_is_attenuation")), nullifier
uniqueness, and authenticated state-root evolution hold of the rows because the
function that wrote them is the verified executor, and the post-state is verified
by construction rather than re-checked. The one characterized hazard is the
interaction between the database engine's error-unwinding and a Lean runtime
mid-stack --- the same shape of runtime-boundary care as the seL4 port
(@sec-sel4) --- and the de-risked alternative runs the executor in a co-located
sidecar reached over a local socket, with the in-backend form gated behind a spike.

== Scope

pg-dregg is a mirror and a light-client verifier backend for the database, not a
full node: the authorization and mirror tiers are circuit-free and live, the
verified-store chain tooth is live, the range proof-attestation and the in-backend
executor are the named horizons, and federation across databases is structural ---
a subscriber replicates the publisher's turns and re-runs the chain tooth locally,
refusing a tampered or reordered stream. @sec-limitations states the in-progress
tiers as checkable facts.
