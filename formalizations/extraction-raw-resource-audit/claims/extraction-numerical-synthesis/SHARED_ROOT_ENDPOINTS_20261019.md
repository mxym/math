# Shared root value and charge

Four modules extend checkpoint `1cf5827b8e39dbd1291c5be34d1fbe70b8b82e80`.
Every earlier source, check, root list and report is preserved byte for byte.

The earlier value-plus-counter implementation computed the scalar root and
then recomputed division inside the annotation helper to determine its root
fuel. Its model was explicitly partial and did not charge that extra counter
work. `SharedBinaryRoot` now stores the numerator, division fuel, quotient,
root fuel and root value once, and returns the value and charge together.
The charge is formed from the same stored fuels, without another call to
division or square root. Its raw value and charge equal the earlier pair;
the same height and partial charge bounds follow internally.

`SharedCostedIntegerEvaluation` and `SharedCostedNumericalProgram` use this
shared root program throughout the actual memoized expression and finite
word recursion. Tuple coordinates and selector scores remain stored vectors,
and only the chosen branch is evaluated. `SharedCostedCompatibility` proves
the entire expression and word result records equal the earlier costed
program, including both the raw result and charge field. Consequently the
sibling actual raw compiler can migrate to the shared implementation while
preserving its established word/error/budget and degree201 charge endpoint.

This avoids a specific redundant division; it does not turn the partial
charge into total machine time. Computing the annotation's ordinary integer
arithmetic, automatic fuel, other arithmetic/comparison primitives, AST and
list/vector construction/allocation/indexing, cache and gate-description work,
and actual target/library provider execution still require separate cost
treatment. Provider output approximation and bit bounds do not imply provider
execution-time bounds. Existing degree201 statements remain root-subprogram
charge semantics, not a full Turing bit-time theorem.
