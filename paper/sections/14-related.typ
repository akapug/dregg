// =============================================================================
// Section 14: Related work
// =============================================================================

#import "../defs.typ": lean
= Related work <sec-related>

Each stub names what dregg takes and where it differs.

*Object capabilities* @elang @eros. The authority model is Miller's: no ambient
authority, _connectivity begets connectivity_, rights amplification via
sealer/unsealers, the Granovetter introduction. dregg's contribution is to
mechanize the *production* law --- non-amplification and non-forgeability as
two-valued, axiom-pinned theorems over the running executor
(#lean("EffectsAuthority.introduce_non_amplifying"),
#lean("EffectsAuthority.amplifying_grant_rejected")) --- and to make every act of
authority receipt-disclosed, hence verifiable after the fact by a third party.

*Macaroons* @macaroons *and Biscuits* @biscuit. Caveated bearer tokens with
offline attenuation are the token lineage dregg inherits; HMAC caveat chains are
on the assumption floor, and token adapters point inward to kernel capabilities.
The difference is that dregg's caveat language is the same predicate algebra as
cell programs and circuit obligations (@sec-guards) --- an attenuation is
checkable by the proof system, not only by the issuing service.

*seL4 / l4v* @sel4. The methodological north star: a kernel whose specification,
implementation, and proof live together, with explicit statements of what is and
is not covered. dregg's analog of the refinement stack is the two-readings
discipline (executor $arrow.l.r$ circuit, welded per effect) plus the assurance
case organized by guarantee; its analog of the l4v assumption statement is the
eight-carrier floor (@sec-assurance). dregg verifies a distributed protocol
substrate rather than a microkernel, and its executable artifact *is* the
verified Lean rather than verified C.

*Mina and recursive-SNARK light clients* @mina. The aspiration "a chain you can
verify on a phone" is shared, and the light-client theorem is the same shape (one
root, recursive verification). dregg differs in what the proof witnesses: not
only consensus-rule validity but per-step authority, conservation, integrity, and
freshness --- the proof attests the protocol's semantics, not just its block
structure --- and the verified statement is about the same Lean kernel the node
executes.

*Ceptre and linear-logic programming* @ceptre. Reading state change as focused
proof search in linear logic informs the substance discipline (value as a linear
resource, verbs as structural rules). dregg fixes the dual orientation: search is
untrusted and lives at the edges (solvers, intent matchers); the kernel only
checks.

*Blocklace / Cordial Miners* @blocklace @stingray. The ordering fabric: a signed
DAG with equivocation exclusion, leaderless finality, and finality tiers as a
lattice. dregg consumes it as the modal half of the step logic --- when facts
become common knowledge (@sec-ordering) --- and gates finality on the verified
rule; its liveness enters the assurance case as the single PostGSTProgress
carrier rather than diffusing through the proofs.

*CapTP / OCapN* @capnproto. The session layer for distributed object
capabilities --- sturdy refs, three-party handoff, promise pipelining --- is the
lineage of dregg's session surface. The kernel-facing difference: a delivered
handoff is admitted only through a verified non-amplification gate
(#lean("AuthModes.captp_granted_le_held")), and session machinery is kept out of
the consensus-visible kernel (pipelining is turn composition; references are
capabilities in slots). The sturdy reference is also the unit dregg's
rehydratable surface (@sec-deos) ships: a persistable, attenuable handle to a
witnessed scene, behind a membrane that re-checks authority at reacquisition.

*seL4 capability description and deployment* @capdl. seL4's capability layout is
itself a described artifact (capDL): the component capabilities are written down
once and a loader instantiates them, so a deployment is reproducible and checkable
at the capability level. dregg's seL4 image (@sec-sel4) places its cell-and-grant
layout in the same relation --- the seL4 capabilities isolate the protection
domains, the dregg capabilities mediate the cells within --- and grounds the inner
graph in the outer one mechanically
(#lean("Firmament.dregg_executor_cap_authority_grounded_in_seL4")). The two
capability graphs are one discipline at two scales, which is the firmament's
distance-parameter claim (@sec-firmament) read from the substrate.

*Secure GUI servers and cross-domain compositors* @nitpicker. The trusted-window
lineage --- a minimal GUI server that mediates input and labels output to keep
domains from spoofing or spying on each other --- is where deos's compositor sits.
The difference is what is *trusted* versus *proven*: a cross-domain compositor
trusts its rendering process to provide isolation, whereas deos makes per-viewer
non-interference a machine-checked theorem about the projection
(#lean("Deos.noninterference"), #lean("Deos.hiddenCell_absent")), with paint
order-independence and the frame property proved of the compositing algebra
(#lean("Deos.paint_order_independent"), #lean("Deos.render_frame_property")). A
window is a capability, so the right to see is separated from the right to act by
construction, not by a window-manager policy.
