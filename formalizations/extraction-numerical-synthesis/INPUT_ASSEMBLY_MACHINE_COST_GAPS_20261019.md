# Remaining machine-cost obligations after list assembly

The numerical338, actual-cache73 and list-assembly13 results concern real
source programs with retained control traces and a specified partial charge.
They do not count every operation of a machine evaluating the whole compiler.
No theorem here treats an arbitrary Nat operation as a unit-cost machine step,
or infers running time solely from bounded output size.

Still requiring actual implementations and simulation bounds:

- Input and control representation: k, p, precisions, recursion/fuel values,
  cache indices and arithmetic that creates or updates them. Current Lean
  Nat parameters are mathematical control data; the declared list/Boolean
  charges do not measure all operations on their machine encodings.
- AST and higher-order closure creation, factor/oracle applications, finite
  function/vector indexing, base-score vectors, cache enumeration, and all
  other list/record/trace construction. Input references eliminated hidden
  online provider evaluation, but not these program-construction costs.
- Allocation, stack/continuation management, sharing or copying of binary
  scalar/packet payloads, and retained-list traversal under one explicit
  encoding. Our list-spine routines copy cells with opaque payloads; a tape
  implementation must specify how payload references or payload bytes move.
- Fixed table and inverse-label data access and actual fixed-library provider
  execution. Finite queried packet heights are not provider running times.
  An efficient provider or a separate concrete provider implementation is
  required; target-provider costs belong to its independently proved source.
- Cost-annotation evaluation itself, if the executable being timed actually
  returns and traverses all retained trace data. The current fee is an
  annotation on underlying value operations, not the runtime of its printer
  or arithmetic projection. A value-only implementation may erase traces,
  but a simulation of that erasure still has to be proved.

Reusable pinned Mathlib infrastructure was inspected read-only at
commit d13f23b723b8a846827a245b89c10fc7d3f11612:

- Mathlib/Computability/Encoding.lean gives explicit finite-alphabet binary,
  list and product encoding/decoding interfaces.
- Mathlib/Computability/TuringMachine/StackTuringMachine.lean supplies TM2
  finite-stack configurations, statements, step/eval and finite support.
- Mathlib/Computability/PartrecCode.lean supplies an explicit program datatype
  and evaluation/representability for partial recursive functions.
- Mathlib/Computability/TuringMachine/ToPartrec.lean supplies a constructive
  simulation into TM2. Its introductory discussion explicitly distinguishes
  the proved simulation from the polynomial-time simulation that is not
  proved there. It therefore cannot be cited as an automatic polynomial
  cost bridge for this compiler.

A narrow follow-up can reuse finite-alphabet encodings and TM2 transitions:
defunctionalize this compiler's finite AST/control constructors into encoded
continuations; implement the existing Bool and list routines on stacks; and
prove a per-transition simulation with explicit overhead depending on bounded
encoded operands, indices and stored structures. General partial-recursive
representability can support computability, but does not replace that timed
simulation. No such whole-machine bridge is claimed in this checkpoint.
