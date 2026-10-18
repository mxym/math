# Actual TM2 subroutine compilation and exact timed lifting

Two new mathematical modules implement and verify actual TM2 statement
transformations for composing concrete finite-stack programs.

redirect maps every local goto through an enclosing label embedding and
replaces halt by goto of the caller return label. Its stepAux semantics
commutes with an explicit configuration map that preserves all stacks and
local memory. The proof of the complete official step iteration preserves
its exact number of transitions, including the last return transition.

The proof does not require a caller-provided invariant asserting absence
of earlier halting. A source iteration ending in some configuration cannot
have stepped beyond halt because lifted none is absorbing; that fact is
proved internally. redirectedRun transports an already proved operational
EvalsToInTime without increasing its steps or its bound. Its generic code
agreement premise identifies literal compiled statements, rather than
assuming the desired runtime or numerical correctness conclusion.

splice is a concrete program with local labels on the left of a sum and
caller labels on the right. It automatically installs redirected local
statements, so spliceRun needs no external code-agreement premise at all.
The specialized counterCall inserts the internally verified binary counter
into arbitrary outer TM2 code; its exact steps are borrowTime as 0 and its
bound remains 2*inputWidth+2. The target label at return is active caller
control, with the exact proved counter output and unchanged other stacks.

Finite label support and running-control cardinality are proved when the
source/caller labels and memory are finite. Local statement depth is exactly
preserved. The concrete binary-counter specialization has only Option Bool
memory; it does not introduce a Nat register, fuel, external final budget
certificate or hidden host interpreter.

This is an operational control-composition theorem, not yet the entire
compiler lowering. An outer loop still needs its own actual transition
proof and explicit input/continuation/payload encoding. The generic theorem
also does not declare an infinite local-memory type to be finite: the
finite-state model claim requires actual finite parameters. The earlier
whole-machine cost boundaries remain open and unchanged.

All prior committed numerical/core files remain byte exact. OWNED feedback
and standard guarded aggregate checks are distinct from independent fresh
or trust-zero replay; frozen scopes do not cover these new unused modules.
