# Whole-trace root subprogram resources

Two new modules extend sealed checkpoint
`330c911982ad26f6e1ece384dd091920f20255ea` without changing any earlier file.

`RootProgramCosts` sums the explicit binary division/sqrt subprogram primitive
counts over the actual scalar/packet expression trees. Selection charges all
alternatives. An expression of budget at most `B` has count at most
`(16*(B+2)+5)*operations`. The same bound holds for the full actual arithmetic
word result. Combining the internally proved cached trace budget of degree137
with its primitive AST operation count of degree64 yields
`cachedArithmeticRun_binaryRootPrimitiveOperations_polynomial`: a bound
`C(n,L)*(p+1)^201` on all of these root subprogram primitives in the actual
cached program. No final complexity or correctness certificate is a caller
hypothesis. The rational-provider variant accepts the explicit cached input
envelopes and derives the corresponding product bound.

`BinaryProgramTrace` records the complete root-internal traces from the actual
binary long division and square-root programs at every represented root
node, including all selector alternatives. If the whole trace's represented
integer budget is `B`, every recorded internal magnitude is at most
`2^(2*B+2)`. Both the dyadic actual cached program and generic rational cached
input interface are bound to this theorem. Thus the recursively nested
intermediate inputs are controlled through the explicit primitive algorithms,
as well as through the AST output heights.

The count charges bounded integer shifts, addition/subtraction,
multiplication, comparison and branch choice as primitives. It excludes
automatic fuel computation and does not assert their machine bit costs.
Rational canonicalization/comparison, allocation/index execution and effective
input provider costs also remain separate. These statements are not a
complete Turing bit-time theorem.

Validation: both new modules and the separate 12-root check pass the allowed
single-module author checker. Standard aggregate and independent replay remain
pending the independent frozen audit's global-lock release.
