# Memoized integer evaluation and the recorded root-charge bridge

Two new modules extend checkpoint `48e647135d9351b32ddf9e4492c3e259be58a8b9`.
All earlier source, checks, root lists and reports are preserved byte for byte.

The old degree201 result remains a theorem about the defined AST resource
budget. It is not retroactively reclassified as a runtime theorem for the
nonmemoized evaluator. The earlier clarification remains valid for that code.

`CostedIntegerEvaluation` defines a new actual finite evaluator returning a
raw integer result and a root-subprogram charge. Scalar/packet operands are
evaluated into stored records. Tuple coordinates are materialized in a finite
vector before `ofScalars` reads their fields; selector scores are likewise
materialized once, and only the chosen branch is evaluated. The output equals
`integerProgramRun`; the recorded charge is at most the prior AST root budget.
The root charge uses the explicitly stated primitive charge of the existing
binary division/sqrt root program. Other arithmetic and memory actions are
not charged by this component.

`CostedNumericalProgram` returns an arithmetic word result and the accumulated
root charge. Base scores are evaluated into a stored vector. The stopping
score and threshold are each evaluated once, and correction branches sum
their actual recursive records. The resulting word, expression list and
comparison count equal the earlier traced recursion. The recorded root charge
is internally proved at most its AST budget, without a caller-supplied cost
certificate. For dyadic literal-cache inputs, the actual new cached program's
root-charge field is therefore bounded by `C(n,L)*(p+1)^201`.

This bridge concerns this new memoized program and its explicit root-charge
semantics. It does not measure the old evaluator, total arithmetic execution,
machine bit time, or Turing time. Ordinary arithmetic/comparison primitives,
automatic fuel, AST construction, lists and vector allocation/indexing,
gate/provider work and cache materialization all remain separate costs.
In particular, dyadic approximation correctness and bounded output bits do
not bound a library provider's execution time. A future total cost theorem
must retain explicit fixed-library provider costs or prove a specified
provider algorithm efficient; mere computability is not sufficient.

The sibling raw packet interface has 20 AST operations per packet rather than
the old literal packet's 1. Its flat integer-budget endpoint already applies,
but its whole operation/root-charge polynomial needs a separately derived
bound; the old literal-input operation theorem is not silently reused.
