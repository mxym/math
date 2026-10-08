# Independent proof-scope and reproducibility audit

**Status:** Written analytic proofs for the theorems in PAPER.md; exact
Gaussian-rational finite regressions; integer-polynomial identity replay.
The paper is not externally peer-reviewed, not Lean-formalized, and
does **not** settle the unrestricted complex six-row tradeoff.

## Proof obligations and discharge

| Claim | Mathematical proof | Independent regression |
|---|---|---|
| Bosonic collision identity | Section 1 symmetrized tensors and multiaffine polynomial factorization | Exact permanent/Gram and collision coefficient comparisons |
| All-width high-weight branch, c >= 5 | Section 2 AM–GM and collision deficit | Integer/Fraction for n=3..8, including disjoint-support equality |
| All-width flat-row exact envelope and equality | Section 3 explicit collision formula, scalar cubic derivative | Gaussian rational phases for n=3..10, endpoint frames, weights below/at/above transition |
| Coordinate-row boundary | Section 4 exact Laplace and two-row Cauchy | Direct minor-by-minor reductions for n=3..10 |
| Flat-row Johnson lift and full spectrum | Section 5 incidence-matrix Gram count and rank | Exact incidence identities and direct minor comparisons for n=3..9 |
| Two-flat arbitrary-third collision (8/3) and equality | Section 8 diagonal-plus-rank-one Schur complement and Jensen | 177 all-complex rational cases, varied third-row magnitudes/zeros and first-row scalings |
| Critical 7/3 on the two-flat locus | Section 8 collision plus Gram AM–GM | Direct permanent-minor/determinant-minor inequalities |
| Sharp six-by-six mixed norm on certified partitions | Section 9 balanced-Laplace Cauchy at 7/3, Hadamard for larger c | Direct 720-permutation permanents/determinants and exact complex norm comparisons for three certified subclasses |
| Rank-one scalar factorization (36) | Clearing denominators and multiplying three factors | Exact bivariate integer-polynomial coefficient equality |
| Stronger Gram shortcut is false | Literal rational witness in Section 6 | Direct exact 22/5 violation |

## Specific risk boundaries

- Section 8 invokes complex Cauchy–Schwarz with an explicitly
  Hermitian positive-definite matrix. For 1/2 < m < 1,
  the diagonal entries are a_j = 1+m Re(r_j) >= 1-m > 0.
  Thus Sherman–Morrison and the weighted inverse are legal.
- In Section 8, m is made real and nonnegative by an allowed
  unimodular row rotation; its definition is the mean of six unit
  complex numbers, so 0 <= m <= 1. At m=1 equality in the triangle
  inequality forces all r_j=1. The two endpoint ranges m<=1/2 and
  m=1 are handled separately; no singular inverse is used there.
- Jensen is applied only with m<1 and denominators
  1+m Re(r_j)>0. It establishes A>=1/(1+m^2), independent of
  sampling, symbolic algebra, or external optimization.
- Section 9 relies only on exact minor expansions, positivity of
  the rectangular bounds, and Hadamard at c >= 7/3; its two explicit
  extremizer families satisfy the certified partition condition.
  The proof does not assert that all matrices are in this class.
- For complex 6-by-6 matrices, the exact checker uses the rational
  criterion R >= 0 and R^2 >= 4c^2|per A|^2|det A|^2,
  where R = M(c)^2 times the product of squared row norms
  less |per A|^2 and less c^2|det A|^2. This is equivalent to the
  claimed unsquared norm bound and avoids all floating square roots.
- The polynomial identity (36) is checked coefficientwise
  in the polynomial ring Z[m,A] by a standalone plain-dictionary
  implementation; the checker does not rely on floating point.
  Positivity of the factored terms is a separate written argument.
- All exact minor checks enumerate the original 3-by-3
  permanents and determinants for Gaussian-rational matrices;
  they do not reimplement their conclusions as test assumptions.
- Numerical optimization and eigenvalue searches are not used
  to justify any theorem or equality classification. They remain
  unproved exploration outside the recorded results.

## Exact replay

At the repository root:

    python3 -B research/three-row-collision-tradeoff/check_exact.py
    python3 -B -O research/three-row-collision-tradeoff/check_exact.py
    (cd research/three-row-collision-tradeoff && sha256sum -c SHA256SUMS)

Both interpreter modes must match results/check_exact.txt.
The included negative control must report the explicitly
positive stronger-Gram-shortcut failure gap 22/5.

**Remaining core gap:** despite Section 9, the unrestricted rectangular inequality
S_6(U)+(7/3)det(UU*) <= 10/3 for every complex unit-row
3-by-6 matrix when at most one row is equimodular and no
row is a coordinate vector. The present methods do not close
that region. In particular, a finite exact replay is not a
universal proof over continuum-many complex matrices.
