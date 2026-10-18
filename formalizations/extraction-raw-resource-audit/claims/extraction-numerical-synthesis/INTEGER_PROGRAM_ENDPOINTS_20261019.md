# Actual integer numerical word program

Three modules extend source checkpoint
`52282c5dfd5c7646919cb2870e081e0e8f14bc11`. All earlier package inputs,
checks, root lists and reports are preserved byte for byte.

`IntegerSelection` gives an exact signed-integer cross-product comparison for
raw fractions, and finite integer min/max selectors equal to the earlier
rational selectors, including their tie handling. Its two comparison product
magnitudes are bounded by `2^(A+B)` when the input fractions have heights
`A,B`. The selectors do not construct normalized rational values online.

`IntegerExpressionProgram` supplies the complete mutually recursive scalar
and packet evaluator. It uses raw integer arithmetic, the explicit binary
division/sqrt root algorithm, and the integer max selector for each Pauli
chart. Its raw output objects equal `integerRun`, including every chart
decision. Its value therefore equals the original rational evaluator.

`IntegerNumericalProgram` uses this integer evaluator for every base-net score
and stopping comparison in the actual finite recursion. Its full result
`integerTracedPairWord` equals `tracedPairWord`, including the emitted label
word, recorded expressions and comparison count. The eager-cache version
`integerCachedArithmeticRun` equals `cachedArithmeticRun` as a complete
result, not merely at a semantic matrix interpretation.

`integerCachedArithmeticSU2Synthesis` internally obtains a fixed finite net
and proves the actual integer-program word length `<=32*L*(p+1)^5`, target
error `<=2^-p`, represented integer budget `<=C(n,L)*(p+1)^137`, and explicit
root subprogram primitive count `<=C'(n,L)*(p+1)^201`. Its online inputs are
the finite library packets, inverse labels and target packets with the
earlier approximation specification. Final correctness and polynomial cost
are conclusions rather than new certificate assumptions. The rational
provider interface remains available for the sibling actual angle compiler.

This is a genuine finite integer word algorithm. It does not yet establish a
complete Turing bit-time theorem. Bounded multiplication/shift/compare and
automatic fuel costs, provider execution and rational packet materialization,
and structural allocation/index costs remain separate obligations. The
efficiently computable fixed gate-set assumption is retained; the fixed net
is offline data and not claimed uniformly computed from arbitrary dense
real matrices.
