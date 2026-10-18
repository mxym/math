# Variable packet fields and actual finite frame skip/copy machines

Four new mathematical modules define a four-symbol finite alphabet:
bit false, bit true, field separator, and endPacket. A packet stores four
signed canonical numerators, each as one sign bit followed by its actual
LSB magnitude bits and a field separator, followed by the positive canonical
denominator bits and endPacket. Magnitudes and denominators remain variable
length. No entire WordIntegerPacket is treated as one alphabet symbol.

The source encoding and explicit field parser consume symbol/list constructors
without Nat or Rat decoding. Raw parsed fields preserve the exact signed
words and denominator; the typed roundtrip reconstructs the very same
WordIntegerPacket using its canonicality/positivity data invariants. The
encoding is injective, and parsing the first encoded cache packet returns
exactly that packet's raw fields and the untouched remaining encoded cache.
Encoding/parsing/normalization execution has not all been lowered to machines:
this checkpoint does not use their output-size bounds as runtime bounds.

The skip machine is an actual official Mathlib TM2 program with three
four-symbol stacks, one label and Option Symbol local memory (five running
control/local combinations). It pops symbols until endPacket. It does not
receive a length or Nat loop counter. The copy machine has two labels and
ten running control/local combinations: it scans each symbol onto scratch,
including endPacket, then restores scratch onto output in the original
order. Their statement depths are at most three and five respectively.

For every actual typed packet p, skipPacketRun constructs official
StateTransition.EvalsToInTime with exact transitions (encodePacket p).length.
copyPacketRun constructs an actual whole copy execution with exact transitions
2*(encodePacket p).length+1. Both stop at precisely the packet boundary;
remaining input and the existing output suffix are preserved, with empty
copy scratch. Terminal states belong to official StateTransition.eval.
The copied output parses to precisely the original typed fields, not merely
to an equivalent rational quaternion. No caller final-cost/result certificate
or precomputed frame length is a program input.

A proved decoded IntegerPacketHeight B implies an encoded packet length at
most 5*B+14, and therefore at most 5*B+14 skip transitions and 10*B+29 copy
transitions. Cache encoding length is exactly the sum of packet lengths,
with the corresponding internal uniform-height bound.

This completes concrete variable frame skip/copy primitives. Binary indexed
whole-record selection still needs to compose a counter whose bit alphabet
is explicitly embedded, frame skipping and copying in one controller. All
precision-index construction and whole compiler/AST/provider/cache encoding,
allocation, remaining scalar primitive lowering and single-tape simulation
remain separate. The source338 budget is not promoted to a whole-machine
runtime theorem by these results.

Earlier sealed numerical/core files remain byte exact. Only OWNED guarded
feedback is performed while the independent audit holds the global build
lock; ordinary aggregate and independent replay evidence must be recorded
separately when available. Earlier frozen scopes do not cover these new
unused successors automatically.
