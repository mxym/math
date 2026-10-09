# Paper-to-kernel correspondence

Source: `notes/four-row-permanent-tradeoff/PAPER.md`, Theorem 1.
This package extends, rather than relabels, the earlier v1 sharp-bound certificate.

| Paper assertion / necessary step | Proved Lean declarations | Scope |
| --- | --- | --- |
| Actual complex matrix, permanent, determinant, Euclidean row norms | `Mat`, `rowSq`, `rowNorm_semantics`, `rowProduct` | Mathlib matrix permanent and determinant, not replacement scalar data |
| Universal sharp bound, including zero rows | `sharp_four_row` | Inherited byte-for-byte from the completed v1 proof |
| Cauchy collision equality, Eq. (13) | `variance_four`, `collision_eq_iff_products_constant` | Equality is proved from a sum of six nonnegative squares |
| Matrix equality forces every row-pair equality | `critical_first_pair_saturated`, `critical_equality_constant_products` | Proved from actual Laplace/Cauchy bounds, arbitrary row relabeling, and strictly positive row norms |
| Disjoint supports imply an actual monomial matrix | `monomial_of_disjoint_rows` | Chosen support columns give a bijection; no assumed classification |
| Intersecting supports force full support | `full_support_of_intersection`, `full_support_of_not_disjoint` | Every nonzero row is handled |
| Three full-support rows force equimodularity, Eq. (14) | `first_row_equimodular` | Product identities, nonzero cancellation and nonnegative squared moduli |
| Critical rank-one factorization | `flat_of_full_support`, `constant_products_dichotomy` | Explicit factors u_i=A_i0/A_00, v_j=A_0j |
| Every listed extremizer attains equality | `flat_values`, `monomial_values` | Actual permanent, determinant and row-product values |
| c=1/2: both classes and no others | `critical_equality_iff` | All matrices with four nonzero rows |
| c<1/2 and c>1/2: select the correct class | `subcritical_equality_only`, `supercritical_equality_only` | Derived using the critical bound and the independently proved determinant bound |
| Zero-row boundary | `rowProduct_eq_zero_iff` | Exact equivalence with vanishing product of row norms |
| Entire Theorem 1, inequality plus all equality cases | `sharp_four_row_complete` | Every actual complex 4x4 matrix and every real c>=0 |
| Optimality, attainment and exact real pencil norm, Corollary 2 | `matrix_bound_iff`, `matrix_attainment`, `exact_real_pencil_norm` | Inherited v1 proof included and rebuilt/replayed |

All names above are in namespace `FourRowTradeoff`.
`Statements.lean` prints the endpoint and the definitions of its two matrix classes.

## Precise matrix classes

`IsFlatRankOne A` asserts an actual factorization A_ij=u_i v_j,
with every u_i and v_j nonzero and every squared column modulus
`Complex.normSq (v j)` equal to `Complex.normSq (v 0)`.
This is exactly the rank-one, equimodular class; it is not a predicate
that assumes equality in the inequality.

`IsMonomial A` asserts the existence of an actual permutation of the four
column indices, one nonzero entry in each selected position, and zero
entries elsewhere. Bijectivity supplies both the row and column condition.

The final theorem does not assume `NonzeroRows`, `ConstantRowProducts`,
a variance identity, or a saturation condition. The only mathematical
hypothesis is the paper's determinant weight c>=0. All support and
saturation bridges are internal theorems.

## Not covered by this certificate

The all-n rectangular theorem (Theorem 3), the quantitative pairwise-deficit
bound (Theorem 4), the convex/power objective extensions (Theorem 4B and
Corollary 4C), and the parity-law/tensor statements (Corollaries 5 and 6)
are not automatically included. The present completion is the entire
Theorem 1, not an assertion that every theorem of the manuscript is Lean-verified.

The general even-row transfer companion is also outside this certificate.
