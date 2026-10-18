# Numerical continuation: represented integer budgets

This extension adds five mathematical modules and a separate 29-root check.
Every file at numerical baseline `263983366e557b5ea74c2b9f405be817823adabe`
is preserved byte for byte. The earlier frozen aggregate and root list are
unchanged. The additional modules are not claimed to be covered by the earlier
independent replay.

`NumericalBitTrace` derives a three-coefficient budget recurrence for the
actual finite `tracedPairWord` program. `BitTraceGrowth` proves explicit
exponential-in-depth bounds, including a remainder bounded by a fixed
constant times `2^(128*depth)`. Since the actual depth is `clog 2 (p+1)`,
`CachedIntegerBudgets.cachedArithmeticRun_integerBitBudget` proves a budget
at most `cachedIntegerBudgetConstant n L * (p+1)^137` for the actual cached
dyadic-input arithmetic run. It derives this from the earlier internal cache
precision bound and the actual provider numerator bound.

`IntegerSubtreeBounds` proves that every represented scalar and packet
subexpression, including all selection alternatives, has raw integer
numerator and denominator magnitude at most `2^B`, where `B` is the trace
budget. This covers the represented AST results; it does not yet claim to
bound every temporary value inside the integer primitive implementations.

`RationalCacheBudgets.cachedArithmeticRun_envelope_integerBitBudget` accepts
explicit flat envelopes for the actual cached rational providers and bounds
the actual full trace by
`1000000000002*(n+1)*(B+2)*(L+1)*2^128*(p+1)^128`.
The companion raw-provider interface `PacketOracleHeight` turns actual
common-denominator input representations into the required envelopes. These
are generic input operand interfaces, not hypotheses asserting synthesis
correctness or the final complexity bound. The sibling effective encoding
extension supplies its actual target packets and their polynomial heights.

The finite word, numerical correctness, cache request counts and primitive
operation count remain the previously proved actual program. This extension
closes the recursively nested represented operand-size budget. It does not
prove Turing bit running time: integer primitive implementation costs,
their internal operands, structural allocation/index costs, and effective
fixed-library input provider costs still require explicit treatment.

Validation at this checkpoint: the five modules were checked in dependency
order by the authorized single-module checker, then the new 29-root check
passed with root axioms restricted to propext/Classical.choice/Quot.sound.
A standard aggregate attempt was stopped while still queued behind the
independent audit's global lock. Standard aggregate and new independent
kernel replay remain separate, pending checks. This checkpoint is not
aggregate or independent replay evidence.
