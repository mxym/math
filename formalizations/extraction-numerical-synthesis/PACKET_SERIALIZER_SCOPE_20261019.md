# Physical native packet serializer and same-stack codec

Four new mathematical modules provide actual native Bool word to framed Symbol
serialization and a single-program parser/serializer roundtrip. They reuse the
same seven heterogeneous stacks and 160-value finite memory of the field parser.

PacketSerializer has 20 labels and maximum statement depth four. It really pops
all previous Bool scratch cells, pushes endPacket onto the existing Symbol output,
reverses the denominator onto scratch, then pops scratch and pushes concrete bit
Symbols. Four numerators are handled in reverse coordinate order: push field,
pop native magnitude onto scratch, reverse it into concrete bit Symbols, and push
the finite sign flag. Each pop, EOF, separator, sign and goto is actual TM2 syntax.
No Nat/Rat conversion, normalized field value, atomic packet append or host list
operation occurs in the finite machine. Original native word fields are consumed;
existing Symbol suffix and sign flags are retained.

serializeRun internally constructs official EvalsToInTime. Exact time is

oldScratchLength + 2*encodedFrameLength + 2.

The final Symbol output is the exact encodeRaw packet prefix followed by the
old suffix, all five input Bool words and scratch are empty, finite flags/status
are preserved and the official terminal state is in eval. Typed source decoding
reconstructs the same packet and suffix. With packet numerical height B the time
is internally at most oldScratchLength+10B+30. Inputs are actual Bool fields and
finite signs; forming a source record is not a machine operation inferred free.
serializeCall provides literal finite caller insertion with the same actual time.

PacketCodecMachine composes the already proved typed parser and serializer on
these very same physical seven stacks. Parser halt is a goto into serializer
clearScratch. Its complete official codecRun has

steps + 1 = 4*encodedFrameLength,

and internally at most 20B+55 for typed packet height B. The actual parser-return
prefix has the original exact native fields. The final Symbol frame and suffix
are identical to the original input, and Bool fields/scratch are again empty.
There are 35 labels, 5600 finite control-memory combinations and statement depth
at most five. No host packet packing or representation copy connects the phases.

This closes per-packet actual serialization/extraction components, not complete
provider/cache/request-generation or AST evaluation. Source packet packaging,
initial native provider computation, cache-list ordering/control, arbitrary bad
stream Option completeness/normalization and a bounded single-tape simulation
remain separate. No source338 or component TM2 bound is promoted to full compiler
machine time. Only new unused source/metadata are added; older inputs and audit
scopes stay byte exact. New strict kind/real-execution fixtures are recorded as
successor verification, never retroactively attributed to prior build-only reports.
