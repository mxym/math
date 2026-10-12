# Source-to-statement review: complete cofactor spectral Theorem 1

Mathematical source: `mxym/math` commit
`df6d94763c852c3cf69f29c5fa95c51f88378160`,
`notes/sharp-cofactor-spectral-asymptotics/PROOF.md` and `sharp_cofactor_extrema.tex`.
This review is by the implementing agent. Fresh compilation, all-owned dependency audit and
empty-kernel replay are separate mechanical checks. No independent human review is claimed.

## Statement and actual objects

`firstCofactor A i j` is the permanent on the row and column complements. Its equality to
`A.submatrix i.succAbove j.succAbove` is proved. The minor is not transposed.
`compound A i j = A i j * firstCofactor A i j`. The permutation-fiber and row-sum identities
are proved for this actual definition and mathlib's official permanent convention.

`complexGram v i j = sum_c v i c * star (v j c)` and the polynomial Fock pairing are linear
in their first argument. Official Euclidean inner products are linear in their second;
the feature vectors are explicitly conjugated to preserve the same matrix entries.

The matrix classes are (i) arbitrary complex Hermitian PSD matrices with positive permanent,
(ii) correlation matrices of **exact rank two**, and (iii) positive-definite correlation
matrices with positive permanent. The real direction class permits complex Hermitian matrices.
It is not the class of real symmetric input matrices.

`largestHermitianEigenvalue` is the first entry of mathlib's antitone sorted Hermitian spectrum.
`largestCompoundRatio` divides this eigenvalue of the actual compound by the actual permanent.
`largestRealCompoundRatio` uses the entrywise real part of the actual compound. Hermitian
diagonalization proves that every Rayleigh value is bounded by this largest eigenvalue. The
official orthonormal eigenvector basis supplies a unit direction attaining it, over both
complex and real scalars. Cofinality then proves equality of the spectral and variational
suprema for every dimension and every admissible matrix class. Empty dimension-zero sets
are handled; no conditional-completeness hypothesis is silently dropped.

`sharp_cofactor_spectral_asymptotics` asserts all six limits in Theorem 1: the complex-direction
spectral extrema divided by `log N` tend to 1 and the real-direction extrema tend to 1/2,
for each of the three matrix classes. There is no construction oracle or desired estimate
in the hypotheses of this endpoint theorem.

## Upper bound

Actual Fock products and coordinate contractions prove the permanent Gram identity and
positivity of the actual compound in every rank, including singular PSD inputs. The indicator
inequality follows from complementary cross sums, finite weighted permutation averaging,
partial-swap normal forms and sums of squared contractions. No indicator inequality or
double-coset positivity is assumed. Weighted averaging replaces the paper's explicit
double-coset cardinality formula and proves exactly the required positivity.

Abel summation, finite Cauchy--Schwarz and an actual sorting permutation, preserving ties,
give the binary norm estimate. Positive/negative splitting gives the real factor `2*S_N`;
the four real/imaginary positive parts give the complex factor `4*S_N`. The square-root
increment bound gives `S_N <= 1+H_(N-1)/4`. The actual Rayleigh and spectral bounds are
`4+H_(N-1)` and `2+H_(N-1)/2`. Official harmonic/log estimates and logarithm divergence give
the sharp leading upper coefficients for all six classes.

## Actual finite lower construction

Finite Gibbs entropy, a geometrically separated mean-index bound and real exponentiation
prove `E(b)=b^(b/(b-1))/(b-1)` for every nonempty positive geometrically separated sequence.
Every selected subset is genuinely enumerated and inherits the entropy bound.

Primitive roots of unity and actual complex roots of nonzero coefficients build the signed
root rings. Their homogeneous products, root sums, squared root sums, squared norms and
imaginary second moments are proved exactly. Disjoint finite indices and a proved bijection
transport the reserve zeros and rings to `Fin N`. A zero and a nonzero slope give a nonzero
two-by-two row minor, and the official Gram rank theorem gives exact matrix rank two.
Unit normalization gives unit diagonal, PSD and positive permanent.

The actual two-color polynomial coefficient identity gives the permanent as
`N! * gamma^2 * sum_j normSq(coeff_j)/choose(N,j)`. Boolean sign characters are orthogonal
over all actual sign choices; the square average remains valid when subset degrees collide.
The finite average supplies an actual sign assignment with permanent bounded by the explicit
binomial-weighted subset sum. The actual marked pure coefficient gives complex slope and
real imaginary-part Rayleigh lower bounds.

## Tail, all dimensions and parameter quantifiers

Log-factorial integral comparison proves the required factorial bound. Descending-factorial
products prove the binomial lower bound. Combined with each subset's entropy bound, these
give the actual subset weight at most `2*e*J*theta^(2*J)`, with `theta<1` proved from the
chosen fixed parameters. Weighted powerset generating products bound the sum by geometric
and weighted geometric tails. These actual infinite sums are proved summable and their
tails tend to zero. Thus the conditional permanent estimate is discharged as `1+eta`.

The degree sequence is the actual recurrence `d_(k+1)=ceil(b*d_k)`. Its positivity,
strict monotonicity, geometric separation and prefix budget are proved, including the
ceiling error. Instead of selecting the paper's maximal number of rings, the formal proof
chooses an explicit floor of `log N/log b` minus a fixed budget offset. This proves the same
sharp leading count and provides a positive reserve in **every sufficiently large dimension**.
It is not merely a subsequence construction.

All parameters are fixed before dimension goes to infinity. The floor error divided by
`log N` vanishes. The actual derivative of log at 1 proves `E(1+t)*log(1+t) -> e` as `t` tends
to zero from above. Choosing `b=1+t`, `delta=eta=t` and
`C=(1+t)*E(1+t)/(e*(1-t))` gives `theta=1/(1+t)<1`. Its leading lower coefficient tends to 1.
Combining these lower bounds with the upper bounds proves all four unrestricted/rank-two limits.

## Positive definite extension and scope

`(A+t*I)/(1+t)` is proved positive definite and unit diagonal for each `t>0` when A is PSD
and unit diagonal. The actual permanent and compound are finite polynomials in matrix entries.
Continuity of their Rayleigh quotient at a matrix with positive permanent and nonzero direction
retains any strictly smaller finite-dimensional bound, with positive permanent retained too.
This proves the two positive-definite limits. The perturbation may increase rank; no exact-rank-two
positive-definite assertion is made for dimension greater than two.

This package completely formalizes **Theorem 1**, including its positive-definite extension.
The later sharp ramp constant and rank-two endpoint/immanant statements in the same manuscript
are separate results and are not claimed by this certificate. The final certificate covers all
78 frozen modules and every owned declaration, with no audit exclusions. Only its exact final
source hashes, not prior checkpoint verification records, support the final replay claim.
