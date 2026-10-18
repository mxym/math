# Actual finite-stack fifths transducer

This new experimental scope is outside the frozen native8b78 scope and every
older audit/manuscript. It implements a genuine official Mathlib TM2 program,
not an independently supplied primitive-fee annotation.

The three Boolean stacks hold a unary precision clock, little-endian numerator
digits, and denominator digits. The only local data are a five-state remainder
and a Boolean flag (10 possibilities); there is one running label. Each label
has static executed-statement depth at most6. The actual code pops one clock
cell, applies the finite transition table, pushes the numerator bit and a false
denominator bit, changes the finite remainder and loops. It starts with empty
numerator and denominator[true]. It has no Nat/fuel/index/counter register.

fifthsRun is an internally proved official EvalsToInTime certificate: exactly
p+1 TM2 transitions for any clock list of lengthp. machine_steps proves those
actual iterated transitions, terminal_stops proves halting, and the terminal
evaluation theorem proves membership in StateTransition.eval. The returned
bits are exactly the original run's numerator and denominatorBits p. The old
strict dyadic error is therefore connected to this actual finite machine.
The Check executes 85 actual transition examples (five states, precisions0..16),
in addition to all selected theorem/model kinds, types and axioms.

The clock is UNARY input. This result does not account for generating it from
a binary precision, marshalling four signed coordinates, canonical Word packet
normalization, the complete library provider, a single-tape simulation-time
bound, or whole compiler execution. TM2 transitions and static finite statement
depth are the precise operational metrics. No complete machine-bit-time or
new independent kernel/negative-control claim follows from author compilation.

Shared Lean4.34.1/Mathlib d13f23b7 remain on D. The generic append/reverse TM2
semantic helper is an explicit fixed local dependency; no active author .olean
is linked, no full Mathlib copy is made, and all frozen sources are untouched.
