# Explicit division and square-root programs

This extension adds six independent modules after numerical checkpoint
`8e7964f021a1039169d4e214fca576220e5e6e4e`. It preserves every earlier
source, aggregate, root list and report byte for byte. Its separate check and
evidence do not extend a frozen independent audit automatically.

`RootOperandTrace` lists the actual integer values in the existing scalar
root operation: clipping, precision and shift counts, the shifted numerator,
division quotient, integer-root input/output, and power-of-two denominator.
For an input height `A` and precision `p`, all these magnitudes are at most
`2^(A+2*p)`. `RootTraceBudgets` proves this along every represented expression
and every alternative of a selection and binds the whole cached trace to the
earlier polynomial budget. Thus these are bounds on actual primitive inputs,
in addition to earlier AST output heights.

`BinaryIntegerSqrt` implements a base-four digit recursion, recursively
processing `n/4` and comparing the candidate `(2*s+1)^2` with `n`. With
automatic fuel `clog 2 (n+1)+1`, its result equals `Nat.sqrt n`. If `n<=2^B`,
there are at most `B+2` digit steps and at most `6*(B+2)` counted bounded
integer primitives. Every recorded internal value, including the candidate
square that can exceed `n`, is at most `2^(2*B+2)`.

`BinaryIntegerDivision` implements binary long division. It maintains
`remainder+b*quotient=a` and `remainder<b`, and its automatic-fuel result is
exactly `(a/b,a%b)`, including the zero-denominator fallback. The digit
primitive count plus denominator test is at most `10*(B+2)+1` for `a<=2^B`.
For positive `b` and `a,b<=2^B`, all intermediate values in its full recursive
trace are at most `2^(B+2)`.

`BinaryRootBackend` replaces both the general division and integer-square-root
calls in the scalar root with these explicit programs. The complete mutually
recursive scalar/packet evaluator returns the identical raw integer objects
as `integerRun`, including identical selection decisions. Its value therefore
equals the existing rational expression evaluator. `BinaryRootResources`
combines the two subprogram traces and proves every internal root value is
at most `2^(2*(A+2*p)+2)`. Its explicitly counted digit/scaling primitives are
at most `16*(A+2*p+2)+5`.

These are finite algorithms and conservative primitive counts, not an
unproved assertion that `Nat.div` or `Nat.sqrt` run in unit time. The automatic
fuel computation, binary shifts/additions/multiplication/comparison,
canonical-rational conversion/comparison, memory/index operations and input
provider bit costs still need explicit implementation cost treatment before
a complete Turing bit-time conclusion. The new root algorithm is bound to the
existing arithmetic evaluator; the whole synthesis word still uses the
previously verified numerical and trace interfaces.

At this checkpoint all six modules were checked in dependency order with
the authorized own-module checker, followed by the separate root/axiom
check. Standard aggregate and independent replay are pending the frozen
audit's release of the global lock. No standard aggregate or independent
kernel replay is claimed by these author-feedback checks.
