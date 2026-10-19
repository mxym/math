# Actual typed packet field extraction into native Bool word stacks

Three new mathematical modules define a heterogeneous-alphabet Mathlib TM2
program with seven physical stacks: one Symbol input, one Bool scratch and
five native Bool word outputs. Four finite sign flags, current Option Symbol
and accepted status form 160 finite memory values. There are fourteen labels,
2240 label-memory combinations and statement depth at most five.

A numerator sign is popped as a concrete Symbol.bit and stored in its finite
flag. Each magnitude bit is popped and pushed on Bool scratch. On field separator,
scratch is popped and reversed onto its designated Bool numerator stack, then
control advances to the next sign. The denominator similarly scans to endPacket
and reverses scratch onto the Bool denominator stack. Success is marked only
at the last actual scratch EOF transition. No runtime Nat decode/index/fuel,
Rat conversion, whole-field list primitive or normalization is used.

The single finite program's complete parseRun has internally proved official
EvalsToInTime and exact steps

2*(sum of four magnitude widths + denominator width) + 14.

Equivalently parseTime+4=2*encodedFrameLength. The initial field outputs and
scratch are explicitly empty. Exact input suffix is preserved, scratch is empty,
all four signs and five Bool words are exactly the original raw fields, and
accepted is true. The final state belongs to official StateTransition.eval.
For an original typed WordIntegerPacket of numerical height B the internal
canonical encoding-volume bound gives at most 10B+24 transitions.

resultRaw is only an observation of native bit-stack/finite-control data; it
uses no Nat, Rat or complex conversion. Its exact roundtrip means that the
original typed canonicality/positive-denominator invariant reconstructs the
identical WordIntegerPacket. These invariants are input representation facts,
not an unproved normalization implementation or final-cost certificate.

This scope proves typed well-formed frame extraction. It does not yet prove
the complete source Option parser equivalence on every malformed stream, or
splice the seven-stack parser into the five-stack master-query reader in a
single heterogeneous stack/memory program. The complete query/frame encoder,
initial output-stack setup or reuse clearing, normalized arbitrary inputs,
record packaging/delivery into arithmetic evaluation and whole compiler
machine bit-time remain separate. Official multi-stack TM2 transition time,
source primitive annotations and single-tape time remain distinct.

Only new unused files are added; previous source and metadata remain byte exact.
OWNED, standard aggregate and independent kernel evidence are recorded separately.
