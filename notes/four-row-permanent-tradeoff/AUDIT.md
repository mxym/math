# Four-row permanent–determinant: proof and exact-replay audit

**Date:** 8 October 2026. Model-assisted audit, not human
refereeing, an external priority check or full Lean formalization.

## Mathematical theorem and dependencies

The new proof establishes for every complex 4-by-4 matrix and all
real c>=0
\[
|\operatorname{per}A|+c|\det A|
\le\max(3/2,1+c)\prod_i\|A_{i,*}\|_2,
\]
with the complete strict-side and critical equality classification.
It also proves an exact quantitative pairwise deficit and an
all-column-width rectangular two-row energy identity.

No prior analytic bound is needed: the proof is derived from
finite Laplace expansions, Cauchy–Schwarz and AM–GM.
The known Carlen–Lieb–Loss sharp *permanent-only* constant
at n=4 is 3/2, and is explicitly attributed.
The determinant refinement is the asserted continuation.
The known three-row complex pencil result is credited; the
four-row proof uses a distinct balanced two-row method.

For the parity subfamily on S4, uniform one-point marginals and
TV=12|t| are calculated explicitly. The sharp complex-valued
L2 radius 1/4 and exact tensor product norm are restricted to
this parity family, **not** arbitrary uniform-marginal laws.

## Detailed audit of the proof

1. The two-row symmetric and alternating minor energies are
   both exact identities, including all complex conjugate terms.
   In the polynomial checker the conjugates are formal independent
   indeterminates, so cancellation proves the identities for
   every complex pair, not just tested inputs.
2. For unit rows, the overlap deficit
   Delta_n=sum_j |a_j|²|b_j|² - |<a,b>|²/n is nonnegative
   by standard complex Cauchy–Schwarz.
   This proves the all-n sharp rectangular theorem and its
   full three-regime equality criterion.
3. The four-row permanent/determinant Laplace expansions
   each have exactly six two-column blocks; each block expands
   to four permutation monomials. The integer polynomial
   checker verifies both identities coefficient by coefficient
   in all sixteen formal matrix variables.
4. Complementation permutes two-element subsets, so the
   two norm inequalities and the final 2D Cauchy–Schwarz
   estimate apply with no missing coefficients.
5. Sharpness is witnessed by the normalized all-ones and
   permutation matrices; the checker reconstructs the exact
   rational permanent/determinant values.
6. Row permutations allow all three perfect matchings, whose
   averaged two-row defects yield the factor 1/6 in the
   explicit global inequality. No sign convention is lost
   because only absolute values are compared.
7. Equality at c=1/2 is more delicate than on the strict
   sides. Vanishing six pair deficits means the coordinate
   product of any two rows is constant across columns.
   Either all supports are disjoint (a monomial matrix)
   or a single overlap makes all rows fully supported;
   the three-row product-ratio identity then enforces
   equimodular columns and rank one. Boundary t=0,1
   of the explicit B_t=(1-t)I+tJ path gives independent
   exact sharpness cases; the interior quadratic deficit
   is verified as a polynomial identity.
8. For parity-biased laws nu_t(pi)=1/24+t sign(pi),
   each prescribed row-image pair occurs in exactly
   three even and three odd permutations. The normalized
   L2 norm factor in four rows is 1/16 of the product
   of Euclidean row norms, yielding the sharp kappa(t).
9. The all-N tensor upper bound applies the one-column
   inequality conditionally, followed by induction on the
   nonnegative row L2 norms. The sharp lower equality
   factors are explicit products of constant or indicator rows,
   and so hold for nonidentical independent columns.

## Exact replay

From repository root:

~~~sh
python3 -B notes/four-row-permanent-tradeoff/check.py
python3 -B -O notes/four-row-permanent-tradeoff/check.py
python3 -B notes/four-row-permanent-tradeoff/check_tensor.py
python3 -B -O notes/four-row-permanent-tradeoff/check_tensor.py
python3 -B notes/four-row-permanent-tradeoff/check_even_transfer.py
python3 -B -O notes/four-row-permanent-tradeoff/check_even_transfer.py
(cd notes/four-row-permanent-tradeoff && sha256sum -c SHA256SUMS)
~~~

The checker outputs must agree byte-for-byte between optimized
and normal modes and with the frozen result files.

The main checker uses exact symbolic sparse polynomials with
integer coefficients; it checks each identity as the equality
of the entire coefficient dictionaries. All witness and
parity calculations use fractions. Its interpolation-path
equality is a true polynomial identity, not a numerical
fit. The separate tensor checker verifies 43,896 exact
permutation-tuple cases across twelve rational parameter vectors,
including nonidentical laws and strict/critical TV cases.
These are **finite regression controls** for the tensor
construction, while the all-N norm is proved in the paper.

No floating-point optimization, stochastic evidence, external
solver or Python assertions on the essential code paths
is used in the final certificates.

## Convex-objective and all-even-transfer extensions

The full power-exponent result is a consequence of **the already
proved** critical tradeoff |per|+(1/2)|det|<=3/2, together with the
Hadamard bound |det|<=1 for normalized rows. Every achievable
normalized pair lies below the segment from (3/2,0) to (1,1).
Convexity and first-coordinate monotonicity put the maximum of every
admissible convex objective at these two attained endpoints.
This yields the exact continuum of exponents r>=1 and all critical
coefficients (3/2)^r-1. The finite 48-instance Fraction replay
checks only endpoint algebra; the continuous real-r theorem is
**mathematically proved**, not extrapolated from integer powers.

The [even-row transfer](EVEN_ROW_TRANSFER.md) follows by exact
Laplace cofactor decomposition and two Cauchy–Schwarz steps for
all even sizes. The orthonormal-row collision-free theorem follows
from the symmetric tensor/Gram permanent coefficient identity.
The companion [exact checker](check_even_transfer.py) confirms the
Laplace sign bijection on all 41,066 permutations through size 8,
ordinary Gram/fermionic Cauchy–Binet and bosonic coefficient identities
on six rational frames. The all-dimension proofs are explicit in
the text; this is not finite-computation extrapolation.

**Unproved:** the proposed sharp 3-by-6 rectangular energy bound
S3+(7/3)det(UU*)<=10/3 product(row norms squared).
No complete six-row permanent/determinant sharp inequality is
claimed by this addendum.

## Remaining boundaries

The nonreal-coefficient 4x4 pencil norm remains open;
the real-coefficient norm is determined completely.
The sharp parity-law radius is not a statement about the
full Birkhoff polytope of uniform-marginal permutation laws.
The all-n rectangular energy theorem does not prove
a sharp n-row permanent/determinant tradeoff for n>4.
No novelty certification, human referee sign-off, or
complete proof-assistant kernel verification has occurred.