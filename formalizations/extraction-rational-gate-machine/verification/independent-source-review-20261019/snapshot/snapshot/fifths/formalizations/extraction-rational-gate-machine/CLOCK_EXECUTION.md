# Binary precision clock machine

This separate successor preserves the original FIFTHS roots, source and evidence.

`RationalGateMachine.BinaryClock.program` is an actual official Mathlib TM2
program with three Boolean stacks, six labels and 18 running control values.
The input is a canonical least-significant-bit-first Boolean binary word. It
uses an inlined finite predecessor subroutine and emits one false clock symbol
per represented unit, with no Nat value, Nat fuel or host callback in the machine.

`clockRun` supplies an official `EvalsToInTime` ending with empty counter and
scratch stacks, and precisely the unary clock followed by its original suffix.
The actual transitions are bounded internally by `(2*w+4)*q+1`, and then by
`(2*clog(2,q+1)+6)*q+1`; the semantic decoded value occurs only in the proof-side
specification. Terminal evaluation membership is proved. `clockTime` is an
external proof-side exact step count and is not an input to `program`.

The check verifies every declaration kind, type and axiom dependency, and runs
195 literal official-machine executions (q=0..64 and three arbitrary suffixes),
checking exact stacks, halting, represented inputs and the logarithmic step bound.
Fixture-only Nat/testBit construction is not part of the executable machine.

This is an author construction/build scope, outside the frozen native8b78
independent audit. Full integration with the fifths machine, four-coordinate
marshalling, canonical normalization, the full provider/compiler machine and
single-tape simulation complexity remain open. Input binary stream preparation
is not charged by this machine theorem.
