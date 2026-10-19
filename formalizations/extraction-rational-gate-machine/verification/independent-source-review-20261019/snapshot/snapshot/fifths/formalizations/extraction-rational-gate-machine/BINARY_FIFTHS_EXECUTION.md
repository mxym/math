# Binary-input fifths transducer

This new successor keeps all earlier provider and clock proofs/evidence fixed.
`RationalGateMachine.BinaryFifths.program` is a genuine official Mathlib TM2
program, with three Boolean stacks, eight labels, 120 running control values
and statement depth at most seven. It consumes a canonical LSB-first binary
precision q, builds the actual unary clock using an inlined predecessor, inserts
the denominator's leading one, then executes the same finite five-remainder
digit transducer. There are no Nat, Int, Rat, decoded precision or fuel registers
in the program. The initial remainder is one of five finite states.

The actual `binaryFifthsRun` ends with exactly the original provider's numerator
and denominator bit words, the correct remainder, and empty clock stack. It
proves terminal evaluation membership, the original strict dyadic error, and an
internal actual-transition bound `(2*w+5)*q+3`, then the canonical-width bound
`(2*clog(2,q+1)+7)*q+3`. Clock construction, denominator initialization and all
digit iterations belong to this single program. Neither correctness nor a final
runtime bound is a caller premise. `StateLift` proves a syntax-directed finite
control lift and exact step/run preservation used by this construction.

The check validates declaration kinds, types and axioms, and runs 165 actual
official-machine executions (all five remainders and q=0..32). It checks literal
output words, independent floor/remainder arithmetic, terminal state and the
same logarithmic transition bound. Nat/testBit exist only in finite fixtures.

This is an author build scope, outside every frozen independent audit. The
initial encoded precision input, four-coordinate packet marshalling, signs,
canonical numerator normalization and full nativeEntry/provider integration
remain separate. Complete compiler machine time and single-tape simulation
complexity are still open. The original fifths and binary-clock scopes are not
expanded or relabelled as independently audited.
