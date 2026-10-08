# Independent semantic review of the six explicit-parameter Bapat sources

This review reads every line of DefinitionBridge, ConstantParameters,
N200EntryBounds, N200RationalEntries, N200EndpointGap, and N200Explicit. It is
not another source compilation or kernel replay. The companion JSON freezes
the six SHA256 values, the written proof version, and the checked ordered data.

The permutation statistic is genuinely the number of inverted pairs, and
DefinitionBridge proves equality of the sum-indicator and filtered-cardinality
definitions. Its q-permanent bridge is equality of the complete permutation
sums; no permutation subclass or proxy is substituted. The endpoint bridge
identifies the real polynomial derivative at one with the real part of the
actual complex q-permanent endpoint derivative.

The positive-definite matrix is exactly the ordered two-column Gram matrix
plus epsilon times the identity. I independently parsed and compared all 200
Lean data rows to the public CSV, in order, and they match. Real and imaginary
entry formulas are the correct a_i conjugate(a_j)+b_i conjugate(b_j) formulas,
and epsilon is added only to the diagonal. The first offdiagonal entry remains
398-i, hence this is complex Hermitian, not a real-symmetric counterexample.

The constants match the written proof exactly: N=19900,
Gamma=N*200!*200*1601^199, K=N*(N-1)*200!*1601^200,
epsilon=1/(4Gamma), h=1/(8K), and q0=1-h. Cast lemmas preserve these rational
numbers; no floating-point interpretation or tunable perturbation remains.

N200EndpointGap proves the endpoint bound for the actual matrix. It imports
the checked integer trace, uses strict integer gap to obtain gap at least one,
connects both actual integer norms to the full Fischer norms via state_eq_200
and the exact-state bridge, and applies the actual rank-two derivative identity.
The main theorem has no negative endpoint/Fischer/certificate hypothesis. The
general transfer theorem it calls does have an endpoint premise, but this
premise is supplied by matrix_endpoint_unit_gap rather than assumed. Its
remaining entry and dimension bounds are also discharged for n=200,R=1600.

The final inequality is the actual q-permanent at q0 versus one, with
0<q0<1 and a positive explicit lower gap h/8. The strict original conjecture
is stated for non-diagonal complex Hermitian positive-definite matrices on the
closed interval [-1,1]. Both q0 and one lie in that interval; the reversed
inequality refutes even non-strict monotonicity, and therefore strict
monotonicity. The original_conjecture_false_from_explicit theorem explicitly
supplies positive definiteness and non-diagonality. Hermitian reality is
separately proved for every real q, so taking real parts is not a weaker
substitute for the original real-valued q-permanent assertion.

I found no scope mismatch or unclosed external premise in these six source
endpoints. This conclusion is a semantic audit of the fixed source version;
it does not assert completion of the root's currently running empty-kernel
verification and does not claim historical priority.
