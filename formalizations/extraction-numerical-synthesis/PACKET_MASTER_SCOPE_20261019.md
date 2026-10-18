# Physical master-cache preservation and full finite packet reader

Four new mathematical modules add a fourth finite-symbol stack, a real
physical working-copy routine and the complete previously proved variable
packet reader in one official Mathlib TM2 program.

PacketMasterClone has two labels. It pops every Symbol from master onto
scratch, then pops scratch and pushes the very same concrete symbol onto
both master and working cache. The exact official transition count is 2T+2,
including both EOF checks. Final master and working cache are independently
represented stacks containing the original exact Symbol sequence. No packet
is an atomic symbol and no persistent-sharing or host list-copy primitive
appears in the machine. Four-symbol bit/field/end framing remains concrete.

PacketMasterEmbedding compiles every old three-stack instruction to a fixed
working-stack label in the four-stack machine, and compiles goto labels.
Halt remains halt. stepAux, actual step and official timed execution commute
with the explicit configuration translation. All original stack reads/writes
are syntactically disjoint from master. The reader phase preserves master
at every actual transition prefix, not only at its final state.

PacketMasterReader installs clone and the old binary-counter/frame-reader
as literal finite labels in one program. There are eleven labels, exactly
fifty-five label/local-memory combinations, and statement depth at most seven.
The binary index is represented by canonical Bool data; the finite program
uses stack constructors and fixed finite memory, never Nat decode, natural
fuel/index arithmetic, runtime packet length or a host subroutine call.

readRun internally constructs StateTransition.EvalsToInTime with bound

(2w+3)N + 4T + 5,

where w is actual binary-index width, N packet count and T actual encoded
cache Symbol length. Exact steps are 2T+2+the previous readTime. Uniform
packet numerical height B implies (2w+20B+59)N+5 via the previously proved
canonical-field encoding volume. No desired final correctness or cost bound
is a caller certificate. Packet/binary canonicality and denominator positivity
are input representation invariants, not cost assumptions.

The actual terminal state belongs to official StateTransition.eval and has:
original master encodeCache ps unchanged; empty scratch; working cache exactly
encodeCache(ps.drop(index.value+1)); and, on a hit, the exact encodePacket of
the original selected typed packet. The source field parser observation is
unconditionally the original selected raw packet, with original typed proof
invariants reconstructing the identical packet, not only an equal value.

This is a complete finite multi-stack machine read starting with a prepared
index and empty working scratch/cache. The retained master supports later
reads; clearing old output/suffix and installing a next query are not silently
free or included in this single-call bound. Initial cache/index serialization,
full typed-field parser and normalization machine lowering, supplying a
stream of queries, integration with native AST evaluator, other primitives,
allocation and single-tape simulation remain separate. We do not transfer
source338 budgets to whole-machine time or infer serialization time from size.
Official TM2 time counts one bounded-depth statement per transition.

Only new unused files are added. Every earlier numerical/core input remains
byte exact. OWNED feedback and guarded ordinary aggregate evidence are
recorded separately; no independent fresh/trust-zero claim is made here.
