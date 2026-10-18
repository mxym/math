# Whole variable-length packet read in one finite TM2 program

Eight new mathematical modules compose a represented binary index, actual
record-boundary scans and whole-frame copying in one official Mathlib TM2
execution over the four-symbol packet alphabet.

PacketCounterAlphabet compiles the actual Bool counter syntax to Symbol
memory and two Symbol-valued counter stacks. Its statically proved WorkFree
property permits any packet stream, including field/end delimiters, on the
untouched work stack. stepAux and every actual step commute with the explicit
configuration map; all counter steps and bounds are preserved. The generic
TM2ConfigurationMap proves exact lifted-transition/time preservation.

PacketStackPermutation compiles constant finite stack roles into syntax,
proving stepAux/step and exact timed-run preservation. It performs no physical
stack relocation pass. PacketRecordPrimitives place the cache on work,
counter/output on left and scratch on right, so the counter, skipper and
copy machine have identical finite alphabets and Option Symbol local memory.

PacketRecordController installs all subroutines as actual finite labels:
four counter labels, one skip label, two copy labels, check and done. There
are exactly forty-five running control/local-memory combinations, and each
label has statement depth at most seven. The controller checks actual stack
constructors, decrements the represented binary counter, scans to the next
packet delimiter, or copies the selected variable frame and stops. It never
uses Nat decode, Nat arithmetic, precomputed packet lengths, runtime fuel,
host procedure calls or entire packets as atomic alphabet symbols.

readRun constructs official StateTransition.EvalsToInTime with an internally
proved bound

(2*w+3)*N + 2*T + 3,

where w is the actual index-bit width, N the number of packets, and T the
actual encoded cache symbol length. The exact external iteration function
readTime is only mathematical time indexing, not machine data. Canonicality
is the input binary representation invariant; packet canonicality and
positive denominator are typed data invariants. No desired final correctness,
execution trace or total-cost certificate is an additional premise.

The actual terminal state belongs to official StateTransition.eval. Its raw
parsed result is unconditionally (ps[index.value]?).map rawPacket. On a hit,
the output stack is exactly encodePacket of the original selected typed
packet, not only an equivalent quaternion; the supplied typed invariants
reconstruct that very same packet. The remaining work stack is exactly
encodeCache (ps.drop(index.value+1)), including out-of-range indices.
A uniform actual decoded packet height B internally implies the bound
(2*w+10*B+31)*N+3 via the proved encoding-volume theorem.

This reader consumes a query stream. Using it for repeated immutable cache
accesses requires keeping a master representation and charging its working
copy or restoration. Construction of the encoded cache/index, machine lowering
of the complete field parser and normalization, further compiler/AST/provider
and scalar primitive lowering, allocation and single-tape simulation remain
separate. We do not promote the source338 compiler bound to whole-machine
time or treat output size as a serialization running-time proof.

All previous sealed numerical/core files remain byte exact. Active independent
19-package fresh verification keeps the shared global build lock; only OWNED
M4000/storage/memory-guarded feedback is used for these successors. Ordinary
aggregate and independent replay evidence must be recorded separately.
