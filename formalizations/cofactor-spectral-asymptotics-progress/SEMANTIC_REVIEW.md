# Semantic review of the complete spectral upper half

This is a source-to-statement review by the implementing agent. The separate fresh compiler,
declaration auditor and empty-kernel checker provide mechanical verification. No external human
review is claimed. The exact mathematical reference is `mxym/math` commit
`df6d94763c852c3cf69f29c5fa95c51f88378160`,
`notes/sharp-cofactor-spectral-asymptotics/PROOF.md` and its typeset TeX source.

## Actual mathematical objects

`firstCofactor A i j` is a permanent over row and column complements. The theorem
`firstCofactor_eq_deletedMinor` identifies it with the standard first deleted submatrix on
`Fin (n+1)`, using `i.succAbove` and `j.succAbove`. There is no transposition of the minor.
`compound A i j = A i j * firstCofactor A i j`. The permutation-fiber identity and row Laplace
identity are proved for these actual definitions.

The official permanent uses its own permutation convention. Its bridge to the row-to-column
mixed permanent is proved, rather than silently changing conventions. `fockPair` is linear in
the first polynomial and conjugate-linear in the second. `complexGram v i j` is
`sum_c v i c * star (v j c)`. For ordinary Euclidean inner products, which are linear in the
second argument, the feature vector is `star (v i)`. This explicit conjugation makes its inner
product equal to the same Gram entry and the norm square equal to the standard `w* M w` form.

## Complete indicator proof

`compound_psd` proves positivity for every complex Hermitian PSD input, with no rank,
invertibility, or positive-permanent hypothesis. Singular inputs are included through the
official PSD square root and an actual Gram factorization.

`compound_indicator_sum` proves
`sum_{i in S,j in S} compound A i j <= card(S) * permanent A` in the standard real order
on Hermitian scalar values embedded in `ComplexOrder`. Empty subsets and the full subset are
included. The proof first identifies the complementary cross sum as a weighted permutation
sum. It averages actual finite coordinate arrays over within-block permutations. Cross-slot
cardinality conservation constructs a genuine partial-swap normal form. Its matrix coefficient
is an explicit sum of squared contractions and is nonnegative. The weighted average equality,
cross-weight invariance and Laplace identities then prove the displayed inequality.

No desired indicator estimate, double-coset positivity, or cardinality formula is supplied as a
hypothesis. A weighted-average proof is used in place of the paper's numerical double-coset
cardinality calculation; it proves exactly the positivity needed for the indicator estimate.

## Complete vector and spectral upper proof

`binaryNormConstant n` equals `sum_{j=1}^n (sqrt(j)-sqrt(j-1))^2`. Abel summation, a
zero terminal coordinate and finite Cauchy--Schwarz prove the sorted nonnegative vector bound.
A lexicographic key preserves all coordinate ties while constructing an actual sorting
permutation. Prefix cardinalities and sums are transported exactly. Positive/negative splitting
proves the signed real factor `2*S_n`; real/imaginary splitting proves the complex factor
`4*S_n`. These are genuine bounds for every finite vector, not assumptions about a spectral norm.

The square-root increment identity proves `S_n <= 1 + H_(n-1)/4`, including `n=0` and `n=1`.
Applying the vector bounds to Euclidean features of the actual PSD compound proves, for every
PSD input with positive permanent and every nonzero direction, the normalized Rayleigh bounds
`4+H_(n-1)` and `2+H_(n-1)/2`. Standard official orthonormal eigenvectors connect these bounds
to every Hermitian eigenvalue. The sorted official spectrum's first entry gives the largest
eigenvalue of `compound A`, and separately the largest eigenvalue of its entrywise real part.

Real test vectors still permit complex Hermitian `A`. The result does not restrict the matrix
to real symmetric inputs. Positive definiteness is used only when selecting that target class.

## Supremum and asymptotic scope

The six variational classes are unrestricted PSD, exact-rank-two correlation, and positive-definite
correlation, each with complex or real directions. All are bounded above by the corresponding
proved Rayleigh bound. Empty admissible direction sets have real supremum zero; the proof handles
this explicitly and does not use a conditional-completeness theorem without its hypotheses.

The official harmonic/log bound gives `5+log(n)` and `5/2+log(n)/2`. The divergence of `log(n)`
proves the eventual inequalities, for every positive epsilon, with leading coefficients `1`
and `1/2` respectively. The rank-two and positive-definite classes inherit those upper bounds;
no existence of an exact-rank-two positive-definite matrix in dimensions greater than two is
asserted.

## Remaining target

This checkpoint completely proves Lemmas 2 and 3 and the spectral/logarithmic upper half of
Theorem 1. It does not prove the signed root-ring construction or every-large-dimension
lower bound, exact rank-two normalization of that construction, the positive-definite lower
perturbation, or equality of the four sharp limits. None of these remaining conclusions is
introduced as a custom axiom or hidden hypothesis. `CofactorTargets` defines the target classes;
definitions alone are not counted as proofs of the missing lower half.

The mechanically verified closure and declaration count must refer to the frozen 38-module
checkpoint. Later development is outside this certificate until separately frozen and checked.


## Verified lower-bound lemmas in this expanded checkpoint

The expanded frozen source set adds eight modules. `finite_gibbs_inequality` proves the finite
relative entropy inequality directly from `log t <= t-1`, for strictly positive finite p,g,
sum(p)=1 and sum(g)<=1. `geometrically_separated_mean_bound` proves the mean-index bound by
shifted sums and the actual adjacent separation inequality. It does not assume the paper's
tail bound. The resulting entropy bound is converted to the exact E(b)=b^(b/(b-1))/(b-1).
`geometric_separation_product_bound` proves the paper's Lemma 4 for every nonempty finite
positive geometrically separated real sequence. Its cardinality is n+1 and the hypotheses
are the actual positivity and adjacent geometric separation conditions.

`signCharacter_orthogonality` proves exact orthogonality over all finite Bool-valued sign
assignments. The square expansion and `groupedSignCombination_square_average` prove the
weighted squared-coefficient average after grouping subsets by an arbitrary finite degree
map. Equal degree sums are allowed. `groupedSignCombination_has_small_choice` proves actual
existence of a sign assignment at or below the finite average. These statements concern
genuine finite sums; no independence or averaging identity is supplied as an assumption.

`marked_coefficient_quadratic_lower` proves that a single factorial-weighted coefficient of
the actual marked polynomial is at most the quadratic form of the actual permanental compound
Gram matrix, in every rank. The polynomial coefficient and the Fock norm are actual definitions.
The proof uses the proved full Gram identity and nonnegativity of all the other terms.

These lemmas have not yet been connected to actual finite root rings. The ring polynomial
factorization, root sums and norms, exact rank-two correlation matrix, factorial/binomial and
subset-tail bounds, every-large-dimension lower estimate, sharp parameter limits and positive-
definite lower perturbation remain unfinished. The finite sign orthogonality theorem alone
does not certify the analytic bound E[R]<=1+eta. The checkpoint does not claim a completed
matching lower bound or equality of the sharp limits.
