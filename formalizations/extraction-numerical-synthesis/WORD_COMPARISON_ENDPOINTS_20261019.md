# Concrete Boolean word comparison

One unused successor module extends checkpoint
`a111f65c7d469886461aad051b4915ec3309ae2c`. Every sealed numerical source,
check, root list and report is preserved byte for byte; the new module is
outside the existing independent raw-resource import closure.

`binaryWordCompareProgram` is an actual least-significant-bit-first Boolean
list algorithm. It recursively compares the two tails, whose bits have higher
place value. A non-equal higher result is returned directly; if the higher
results are equal, it compares the two current Booleans. Missing bits are
false, so leading zeroes do not require canonicalization. Its value path uses
only Boolean/list/Ordering pattern matches and stored recursive results;
it never compares the interpreted unbounded natural numbers.

The result includes the actual branch trace as a tree with one stored child.
The trace records input-head presence and whether the high result was kept
or the low bits compared. It does not append recursive trace lists. The
correctness theorem identifies the returned ordering with the interpreted
natural-number order. The Boolean LE wrapper is true exactly when the first
value is at most the second.

The trace depth is at most `max(lenA,lenB)+1`. In the explicit finite
Boolean/list/record action model, a terminal costs 4, a frame costs 12 plus its
recursive child, and its actual choice costs 2 or 4. The charged trace is at
most `16*(max(lenA,lenB)+1)`. These are stated action semantics for this
specific concrete algorithm, with the charge derived from its returned
execution branch tree rather than an unrelated counter.

This is not a general Turing-machine simulation or a complete compiler
bit-time theorem. Composition with the other bit-list arithmetic routines,
signed integer operations, division/sqrt, providers and the whole compiler's
AST/list/vector construction and indexing remain separate work.

Validation at this checkpoint uses the authorized single-module checker and
a separate root/axiom check. Standard aggregate and new independent replay
remain pending the frozen audit's global-lock release.
