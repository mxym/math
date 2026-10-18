# Binary represented index and actual finite borrow machine

Five new mathematical modules close a concrete Nat-free binary predecessor
backend and use it in an actual list lookup value program.

BinaryCounterMachine.program is an explicit official Mathlib TM2 machine.
It has four labels (borrow/drain/restore/clear), three Boolean stacks, and
Option Bool local memory: exactly twelve running control/local combinations.
Each label executes at most seven statement constructors. No transition has
Nat registers, Nat arithmetic, encoded-value decoding or runtime fuel. The
third stack is untouched, allowing separately retained Boolean data.

For a canonical LSB-first input of numeric value q, counterRun constructs
StateTransition.EvalsToInTime of the official TM2.step. Its terminal counter
is canonical, has value q-1 (saturating zero), has no greater width, empties
the scratch stack and preserves the work stack. The terminal state belongs
to official StateTransition.eval. The machine's internally proved count is
at most 2*inputWidth+2. A represented height bound q<=2^B implies at most
2*B+4 actual transitions; q<=P implies a conservative 2*P+4 bound. The only
input premise is the representation invariant of canonicality, with no
caller final correctness/time certificate. borrowTime is an external
mathematical iteration index, not a number computed by the finite machine.

BinaryIndex stores Boolean input data and its erased canonicality proof.
binaryIndexedLookup matches the cache-list and represented-index constructors,
stores each predecessor and recursive result once, and never calls the
specification-only value decoder, Nat predecessor or host indexed access.
Its returned value equals nativeListLookup at the decoded mathematical index,
and hence ordinary getElem?. Its actual trace retains every predecessor input.

counterTransitions sums the exact official counterRun lengths associated
with those retained calls. It is bounded by
(2*initialIndexWidth+2)*cacheListLength, with at most cacheListLength calls.
This is a bound on proved operational counter macros, not the full outer
lookup machine runtime or the execution time of the fee annotation.

Remaining boundaries: this checkpoint does not replace all precision-index
construction inside the whole input AST or lower the complete outer lookup
loop and arbitrary packet payloads to a finite-alphabet machine. Generic
list payloads are not a single finite symbol without an explicit encoding.
Provider/AST/closure/cache construction, general precision/control paths,
allocation/encoded payload movement, continuation composition and annotation
erasure/execution remain obligations. No full compiler machine bit-time or
uniform338 machine theorem is claimed. Existing source numerical bounds
are not silently substituted for these missing simulations.

All earlier numerical and frozen b288 circuit files remain byte exact.
OWNED feedback and standard guarded aggregate checks are not independent
fresh/trust-zero audits. Earlier frozen scopes do not automatically include
these newly added successor modules.
