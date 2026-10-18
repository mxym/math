# Actual descriptor generation: source audit and next model

Source checkpoint: own bec8b22e72a55abd171ea8a95369d30f9ea29dde. This is a
source-level plan, not a Lean complexity theorem or a new runtime claim.

- EffectiveEncoding/Enumeration.lean: SHA256 `0f2aa117988d43c8b7c509837aa7c7a20b3e0ccb7824058c2f722d1854f14f3a`
- EffectiveEncoding/Elementary.lean: SHA256 `9848a546e6a0e78a5bfde1980c3ff65b1dd82376d08fd6e3bb8470668db9fd64`
- EffectiveEncoding/GrayCompiler.lean: SHA256 `f8739bf08d31e3bcbf5e19fdac0ec3569f7951c5afcf5ba7bf6c6895ae40409c`
- EffectiveEncoding/RawCompiler.lean: SHA256 `d464dda9f998404f9a3286fdce7f843545f7669cf3bb52d4af443708fccd9f58`
- EffectiveEncoding/Occupation.lean: SHA256 `945e8e8933815ccb437054c5586a5b34c0ef6a44a63dba161896111d6d8384b3`
- EffectiveEncoding/Compression.lean: SHA256 `b48e277618ba89602a6473c6eef51d9a9d8651fafc1aa6c647a7addf4a03d145`
- EffectiveEncoding/Extraction.lean: SHA256 `71f110f423531277842001e25a4972908b3596aacbe6f1957dea1f001a3a8941`

The runtime root is Extraction.extractionCode (line35): compressionCode k,
then shifted Bell preparation and list append. decode is absent from this
call graph. compressionCode (Compression:123) descends k stages, shifts the
already produced prefix, and appends stageCode. Thus repeated prefix copying
and shifts must be charged; the final gate count alone does not do this.

A stage (Compression:107) constructs occupationStepCode, extends its wires,
and constructs both allBranchCode and alignmentCode. Each uses its own
occupations(k+1) call. No global occupation/rank cache is present in this
source. Enumeration.triples makes all (k+1)^3 candidates then filters their
sum; occupations maps accepted candidates to four replicated letter lists.
rank regenerates that table and idxOf scans its multiset values. Multiset
permutation/equality cost is not one bit operation. compactEncoding evaluates
rank, then exposes the stored rank index's bits; the proof of injectivity
is erased and must not be included in runtime.

A branch (Occupation:156) has <=4 occupied letters. occupiedPivot builds the
support and takes its minimum. explicitOthers sorts at most3 other letters.
countProgram has one merge per other letter; indexedCount evaluates at most4
embedding equality tests per call. The expression c(q) occurs both in the
merge node and accumulator update. Its computation must not silently be shared.
branchEmbedding calls compactEncoding on the erased occupation, so it triggers
fresh rank generation whenever evaluated; finite function closures do not
supply a global rank cache.

Each raw merge/swap compiles via GrayCompiler.rotationCode/swapCode.
differingWire filters <=n coordinates, otherWires sorts <=n, and moveCode
visits <=n coordinates. swap/rotation explicitly let-bind their generated
move word, sharing it before reverseCode. In contrast Elementary.parityCode
has two syntactic cnotCode calls, and selectedCode constructs masks n on each
call. masks visits exactly2^n indices; maskOfBits filters n coordinates, and
maskParity/control construction sort <=n items. This exponential in n is
polynomial in stage k only because n=activeWires k and the existing proved
activeDimension_polynomial gives 2^n<=16*(k+3)^3 (width logarithmic).

Alignment (RawCompiler:90) visits all occupations. p is an Equiv.swap
composition, not a random-access table. Each step writes p(e i) and f i twice,
in its output swap and its next-permutation update. A valid model must either
analyze the evaluated closure/endpoint representation, or introduce an explicit
stored permutation representation and prove the produced WORD is unchanged.
Treating p(x) as an O(1) table lookup is unjustified. Under strict evaluation,
swap endpoints are evaluated values, but these values are themselves bit
functions; their remaining coordinate evaluation costs still need accounting.

Next formal boundaries, in priority order:

1. Counted enumeration/filter/map/index routines with erased value equal to
   the actual triples/occupations/rank. Prove exactly(k+1)^3 predicate calls,
   <=(k+1)^3 occupation constructors and equality requests per rank. These are
   request counts; additionally model occupation literal replication/append,
   equality implementation and Nat arithmetic before claiming bit cost.
2. Replace alignment's implicit permutation closure stack by an explicit
   stored endpoint stack or finite table; prove the same GateCode list. Charge
   each endpoint equality/coordinate request and every table/stack traversal.
3. Count actual Gray/mask construction and concatenation, including repeated
   local calls; prove erasure to selectedCode/RawCode.compile/stageCode and
   then extractionCode. Compose polynomial event bounds using the proved
   active dimension. Do not infer generation work from final gate count.
4. Join finite-label output concatenation to the numerical word calls and
   already proved output serializer. Counter arithmetic is a ghost annotation
   unless a further execution theorem explicitly charges its evaluation.

The fixed library packet routine must retain its own per-call cost contract
or cumulative provider fee. Output width/precision alone does not imply fast
computation. The target raw packet provider is a closed integer algorithm,
but all its own binary roots and arithmetic must be separately charged; the
online rootCharge annotation deliberately excludes cache creation.

No complete generation model, polynomial bit time, or Turing simulation is
claimed by this document. All frozen mathematical files stay immutable.
