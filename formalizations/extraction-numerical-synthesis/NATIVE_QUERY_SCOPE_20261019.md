# One finite reusable query-to-native-packet machine

Seven new mathematical modules compose the complete physical framed master
cache reader and typed packet field parser in a single official Mathlib TM2
program. There are eleven physical stacks: the previous five Symbol stacks
(index/payload, scratch, working suffix, immutable master, query stream), plus
six Bool stacks (scratch, four numerator magnitudes, denominator). Every
alphabet has at most four symbols. Four signs, current Symbol and accepted
status form 160 finite local memory values; 36 labels yield 5760 finite
running control-memory combinations, with statement depth at most seven.

NativeQueryReaderEmbedding compiles actual reader syntax to the joined stack
and memory representation. Its exact stepAux/step/official timed simulation
preserves every Bool output stack and the finite extra flags. This is a fixed
label/memory representation change, with no physical Symbol copying hidden
inside the proof map. Every reader scan, binary decrement and master clone
still performs its previously proved actual concrete-cell transitions.

NativeQueryParserEmbedding maps each parser input read onto the actual reader
output Symbol stack and maps its native scratch/fields onto the new Bool stacks.
All other old Symbol stacks remain exactly untouched. Each push/pop/peek/load/
branch/goto/halt is compiled as real syntax. Exact operational/time simulation
is proved on the heterogeneous stacks; no packet atom or host field parser is
introduced by composition.

NativeQueryController and ClearRuns add six actual destructive loops. Every
previous Bool stack cell and EOF is popped, then the finite flags/status/current
cell are actually reset before goto reader entry. Exact time is V+6, where V
is the actual previous Bool-stack total length. The reader itself clears all
three old Symbol work stacks, consumes and reverses the actual next framed
binary request, performs two physical master clone passes, and selects/copies
the variable packet. Reader halt is a literal goto into the native field parser.
There is no host reset, host call or value adapter between these phases.

nativeQueryRun constructs official EvalsToInTime for this one constant finite
program, starting with arbitrary previous Bool outputs, arbitrary previous
Symbol work contents and arbitrary finite local memory. Its internally proved
bound is

V + S + 2w + (2w+3)N + 4T + parseTime(packet) + 16,

where S is actual old three-Symbol-work-stack volume, w actual represented
binary-query width, N packet count, and T actual encoded cache symbol length.
The theorem's address-validity premise ps[index.value]?=some packet is an input
address specification, not a desired output/error/cost certificate. Binary and
typed packet canonicality/positive denominator are input representation facts;
no final-correctness or total-budget certificate is added as a caller premise.

Uniform actual packet numerical height B internally yields

V + S + 2w + (2w+20B+59)N + 10B + 40.

The final official eval state contains the exact original four signed Bool
magnitudes/sign flags and denominator, accepted=true, empty Symbol payload
(consumed by the real parser), empty native/Symbol scratch, original immutable
master byte/symbol sequence, exact unconsumed query tail, and exact remaining
working cache suffix. The observed native fields reconstruct the very same
WordIntegerPacket. This observation uses no Nat/Rat/complex conversion;
record packaging into a source evaluator is not silently charged as free.

NativeQueryReuse proves exact re-entry data/memory equality for a literal CPS
return selecting cleanup. Every bit of the actual previous terminal is retained
until the same program pops it. Previous native volume is internally at most
5B+5 and previous Symbol work volume at most T, so a complete next native read
from that actual terminal has internally derived bound

2w + (2w+25B+73)N + 15B + 45.

No old-output height, cleanup-time certificate, free release or zero-cost
re-preparation is required. nativeQueryCall exposes literal insertion into a
specified finite caller; returned_reentry proves control return compatibility.
This is a reusable subroutine endpoint. A complete arithmetic consumer and its
unbounded request-generation/controller have not yet been compiled as one
whole machine; an arbitrary caller's own behavior is not inferred or charged.

Input master/query streams are supplied as actual encoded input. Their initial
serialization/construction from native compiler metadata, malformed-stream
Option parser completeness, arbitrary-data normalization, source record/list/
closure packaging, native scalar/AST evaluation and provider/gate algorithms,
allocation and bounded single-tape simulation remain distinct obligations.
Defined source338 primitive sums, this actual multi-stack TM2 component time
and whole-compiler machine bit-time are not conflated.

Only new unused files are added. All earlier mathematical sources and metadata
remain byte exact. OWNED/ordinary aggregate/independent kernel evidence are
explicitly separate; no fresh/trust-zero replay is asserted for this successor.
