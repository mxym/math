# Canonical binary-input fifths transducer

This separate successor preserves all prior source and frozen audit ranges.
It adds a genuine finite trim machine (three Boolean stacks, three labels,
nine control values, depth <=5). A physical drain reverses the input onto the
empty scratch stack; leading high zeros are popped there; remaining bits are
physically restored to the input. Every denominator symbol is preserved. Its
official run has <=2w+3 actual transitions and outputs exactly the existing
binaryTrimProgram bits, including all-zero and high-zero-padded inputs.

NormalizedFifths.program composes the preceding full binary-input fifths
machine with this trim by literal finite goto syntax. This same program
constructs the unary clock, initializes and emits the denominator, emits the
fifths digits, and normalizes the numerator. It has eleven labels,165 finite
running control values, three Boolean stacks and statement depth <=7. The
actual normalizedRun includes all phases and is bounded internally by
(2w+7)q+6 and then (2clog(2,q+1)+9)q+6. Exact canonical magnitude, unchanged
denominator, empty scratch, terminal evaluation membership and the original
strict dyadic error are proved. LabelLift preserves every literal operation,
step and complete timed run while renaming labels; it does not add host calls.

New checks validate every selected theorem/definition kind, type and axiom,
and execute 384 literal trim runs (all seven-bit words and three arbitrary
denominator suffixes) plus165 complete normalized runs (five remainders,
q=0..32), with independent floor/remainder/value and exact-stack assertions.

This is an author construction/build scope, outside native8b78 and every old
independent audit. Initial precision input generation, signed zero selection,
four-coordinate/nativeEntry packet composition, full provider/compiler machine
time, and single-tape simulation complexity remain open. A complete arbitrary
packet normalization or full compiler theorem is not claimed.
