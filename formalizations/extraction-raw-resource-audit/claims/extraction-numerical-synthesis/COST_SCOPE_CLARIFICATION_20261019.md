# Cost-scope clarification after independent reading

The sealed degree201 theorem bounds the recursively defined AST budget
`binaryRootPrimitiveOperations`. It is not yet an operational running-cost
theorem for the evaluator at checkpoint `e96f1c1`.

In particular, that checkpoint's `PacketExpression.integerProgramRun`
passes a score-evaluator function to `integerMaxIndex`. The selector can
read a previously winning score again, so without explicit memoization
the score AST can be evaluated more than once. The AST budget counts
each score tree once. No general bridge between those two evaluations
has yet been proved. The integer evaluator, word equality and numerical
correctness conclusions are unaffected.

The intended follow-up is a new evaluator that explicitly materializes
the finite vector of raw score results, and returns a cost record along
with its value. It must prove that actual recorded root-subprogram cost
is bounded by the existing AST budget and then propagate that bound
through the actual finite word recursion. Until that bridge is present,
degree201 remains an AST resource budget, not an execution-step bound.

Likewise, the raw packet embedding's constant20 is an AST operation count,
not a measured runtime or a Turing bit-time theorem. New Boolean/list
addition and multiplication carry their explicitly stated finite action
model; integration into the whole backend remains separate.
