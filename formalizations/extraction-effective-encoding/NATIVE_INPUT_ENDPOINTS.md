# Actual bounded merge masses to native Boolean literal data

Only successor files are added. The established prepared-mask/native/Boolean
compiler and all earlier source/configuration/evidence remain sealed.

`unaryWordEncoding n` uses Nat structural recursion to execute n actual Boolean
ripple-carry additions of the literal [true], trimming each resulting word.
The previous run, addition and trimming are stored once, and every actual
addition/trim trace is retained. The program calls neither Nat.bits nor a
semantic Int/Rat conversion/decoder. Its returned word has value n, is canonical,
has length at most clog2(n+1)+1, and its trace has exactly n increments. The sum
of the existing addition and trim Boolean/list models is at most 32*(n+1)^2.

`nativeMergeInputProgram A B` executes two such encodings, then one Boolean add
and one trim for the common denominator. Both returned WordIntegerScalar payloads
reuse that same stored denominator. Their complete raw decoded fractions equal
integerFraction A/(A+B) and B/(A+B), including numerator and denominator rather
than only rational value. For A+B<=M, the actual increment/add/trim traces cost
at most 100*(M+2)^2 and both fractions have height at most binaryWidth M, hence
actual canonical word widths are logarithmic in M.

`prepareNativeSingleInput` prepares those literal payloads once independently
of all later precision queries, preserving signs/half-angle counts and inverse
syntax. It stores records from the real conversion programs. Degenerate atoms
skip conversion just as the prior raw providers skip their root computation.
For every actual descriptor emitted by preparedNativeDescriptorRun k, the sum
of these real preparation trace annotations is <=200*(4*k+2)^2, derived internally
from the proved emitted descriptor mass bounds.

This checkpoint supplies actual WordIntegerScalar data ready for the native
literal/cache interfaces. It does not yet replace the half-angle/phase/packet
target provider or instantiate the native online synthesis. Those bridges belong
to the next successor; no old degree338 bound is silently applied to native ASTs.

The action field counts only the existing Boolean/list increment/add/trim
program trace models. Nat recursion control and degenerate Nat tests/arithmetic,
outer wrapper/record/list allocation, preparation syntax traversal, annotation
maintenance, serialization, and every other provider/compiler fee remain
separate. No complete adapter/Turing runtime is claimed from this projection.
For bounded actual masses poly(k) conversion suffices; no polylog claim is made.

Validation: a new explicit standard full root kind/type/axiom check includes
small actual Boolean-word examples (13 and 3/8,5/8), and prints the conversion
and preparation bodies. Later independent successor replay remains separate.
