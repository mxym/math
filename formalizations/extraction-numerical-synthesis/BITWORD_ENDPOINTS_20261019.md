# Actual Boolean word addition and multiplication

Two modules extend checkpoint `33f1f708be8cb1b03361ab47969830664085c0d6`.
Every earlier package source and report is unchanged.

`BinaryWordAddition` represents a natural number by a least-significant-bit
first `List Bool`. Its full adder uses XOR, AND and OR. The actual recursive
`binaryAddCarry` computes the sum of the two input values and the carry, and
its output length is at most `max(inputLengths)+1`. In the explicitly stated
Boolean/list action model, twelve actions per processed digit and one final
action give an upper bound `12*(max(inputLengths)+1)`.

`BinaryWordMultiplication` is a schoolbook program using only Boolean
branching, consing a zero bit, and that full-adder program. Its interpreted
value is exactly the product; no unbounded natural multiplication is used by
the program definition. The output length is at most `lenA+2*lenB`. If both
inputs have length at most `B`, the explicit Boolean/list action counter is
at most `72*(B+1)^2`.

These are actual finite bit-list algorithms with correctness, allocation
length and explicit primitive action count theorems. The counter is a stated
Boolean/list cost semantics, not a proof about an arbitrary Lean runtime or
a general Turing-machine simulator. Their integration as implementations of
the remaining bounded primitives in the whole numerical backend, together
with comparison/shift/fuel/provider and structural costs, is still separate.
