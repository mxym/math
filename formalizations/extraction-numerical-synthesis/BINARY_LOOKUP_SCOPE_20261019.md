# Entire finite Boolean lookup controller with binary represented index

Two new mathematical modules lower the represented-index Boolean list
lookup to an actual official Mathlib TM2 machine. The machine's six labels
are the four inlined counter labels and two caller labels (check/advance).
Its alphabet is Bool on three stacks, with Option Bool local memory, giving
exactly eighteen running control/local-memory combinations. Every label
has statement depth at most seven.

The caller checks the cache stack and counter stack for emptiness. If the
counter and cache are both nonempty, it executes the compiled binary counter
subroutine, returns to the advance label, pops one cache cell and loops.
The finite return-label compiler is actual syntax in this same TM2 program.
There is no host function call, Nat index, Nat predecessor, encoded-value
decoding, general Nat arithmetic or runtime fuel register in these transitions.

lookupRun constructs StateTransition.EvalsToInTime of the official TM2.step,
with an internally proved bound

(2*initialIndexWidth+4)*cacheListLength+1.

The terminal state is proved to occur in official StateTransition.eval;
its cache-stack head is exactly cache[index.value]?. Canonicality of the
provided binary index is an input representation invariant. There is no
caller-provided final execution, correctness or cost certificate.

The exact operational/source bridge is also proved:

lookupRun.steps = binaryIndexedLookup.trace.counterTransitions
                + 2*binaryIndexedLookup.trace.counterCalls + 1.

Each counterTransitions summand was already the exact number of official
TM2 transitions of a real verified counter invocation. This new theorem
includes the outer lookup control in one actual machine execution; it does
not merely attach a new artificial fee or infer runtime from equal outputs.
A binary input-height bound value<=2^B gives the explicit run bound
(2*B+6)*cacheListLength+1.

This checkpoint reads Boolean cells. It does not treat an entire unbounded
WordIntegerPacket as one finite alphabet symbol. Packet delimiters/encodings,
selection of whole encoded records, construction of precision indices and
all compiler/cache/AST/provider/continuation lowering still require separate
proofs. It does not promote the source338 compiler budget to a complete TM2
or single-tape machine bound. The cost of interpreting/printing the proof-side
time function is not part of the value machine.

Earlier sealed numerical/core files remain byte exact. OWNED feedback and
standard guarded aggregate checks are separate from independent fresh or
trust-zero evidence; old frozen scopes do not include these successors.
