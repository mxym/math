# Raw integer packet input interface

`RawIntegerPacketExpressions` adds an input embedding after checkpoint
`e96f1c105671f715801c714ffefb38e8d1674c5d`. It avoids converting an
`IntegerPacket` through its rational value and then extracting canonical
numerators/denominators.

`rawScalarExpression` embeds numerator and denominator integers separately
as denominator-one literals, multiplies the former by the latter's formal
inverse, and is evaluated by `integerProgramRun` to the identical raw scalar.
`IntegerScalar.ofRat_intCast` proves the integer literal wrapper is exactly
`ofInt`. No fraction normalization, division, or rational comparison is used
for this input embedding.

`rawPacketExpression` assembles the four scalar coordinates. Its integer
program output is `ofScalars` of those original coordinates; consequently its
common denominator is the fourth power of the input denominator and its
value equals the original packet. Input height `B` gives raw output height
`4*B`, expression integer budget at most `8*(B+1)`, and exactly 20 expression
operations. The oracle interface supplies the corresponding flat budget
envelope from actual provider packet heights.

The sibling effective encoding extension owns the raw target provider and
eager raw cache program. It can feed this interface to `integerTracedPairWord`
and use the proved value identity to bind its emitted word to the existing
numerical correctness theorem. This module alone does not assert the whole
provider/cache pipeline's bit running time.
