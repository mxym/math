# Ordinary proof check and remaining connection

The manuscript's flat-average argument is mathematically consistent for fixed
`D` and `1 ≤ s < D`. The degree is `g = s(D-s)`, and the constant is

`c = s^(-g) / product_(i<s,j<D-s) (s+j-i)`

with zero-based indices. The shifts are all positive. The new Lean product uses
exactly these shifts. The actual coordinate Haar average and its exact support
are now derived internally, including singular densities and blocklength zero.

The actual mutual centralizer statement is also proved. A finite Fourier phase
frame gives the diagonal tensor powers from unitary tensor powers; singular
polar factorization extends this to all matrix tensor powers. The reverse
centralizer follows from an internal finite-dimensional bicommutant proof using
orthogonal projection on the vectorized matrix algebra and amplification.
This does not yet label irreducibles or establish the Weyl dimension formula.

The remaining representation-theoretic bridge must prove, for actual tensor
matrices, that on each shape with at most `s` rows the average eigenvalue is
`u_shape(s)/(s^k u_shape(D))` with multiplicity `u_shape(D) v_shape`. It must also
derive `sum u_shape(s) v_shape = s^k`. Defining a structure with these identities
as fields would leave the central mathematics unproved.

After that bridge, cancellation of within-block Weyl factors gives the cross
ratio `R`. Its two expectations give `r/s^k = E R` and
`s^k Tr(Ω²) = E(1/R)`. Exponential concentration near the uniform row vector
then gives both scaled expectations. The reciprocal argument requires an
additional tail estimate: outside a fixed sufficiently small neighborhood,
`k^g/R ≤ k^g` since `R ≥ 1`; the exponential tail defeats this polynomial.
Convergence in probability alone does not establish the reciprocal moment.

An alternative exact identity now proved in Lean is
`Tr(Ω²) = integral_U [Tr(X U X U†)]^k`. For flat `X`, a Grassmannian overlap
Laplace/Jacobi calculation could replace the Schur second-moment calculation.
That route would still need an independent sharp support-dimension theorem.

Primary sources checked:

- [Collins and Śniady, *Integration with respect to the Haar measure on unitary,
  orthogonal and symplectic group*, Section 2](https://arxiv.org/abs/math-ph/0402073):
  the unitary Schur–Weyl decomposition and the Haar conditional expectation.
- [Keyl and Werner, *Estimating the spectrum of a density operator*](https://arxiv.org/abs/quant-ph/0102027):
  tensor/permutation decomposition, character probabilities, highest-weight
  bounds and exponential concentration of normalized row lengths. Its proof
  sketch explicitly starts with nonsingular input; the flat rank-s law should
  be established on the s-dimensional support before its embedding into D.

The fixed Mathlib source has general Schur's lemma, Young diagrams and
semistandard tableaux, finite group representation theory and Haar measure.
It has no existing Schur polynomial, Specht module, classified Schur–Weyl
decomposition or hook/Weyl dimension theorem at the pinned revision.

No source in this package assumes the final rank or purity asymptotic.

The Haar conditional expectation has now also been reduced to an actual finite
matrix calculation. The literal integral equals the Hilbert--Schmidt projection
onto the span of the genuine copy permutations, with the orthogonal projector
constructed internally. This includes `D < k`, where permutation generators are
linearly dependent and a full permutation Gram matrix need not be invertible.
For flat input its exact Gram entries are `D^(number of cycles)`, and its
moments are `s^(-k) s^(number of cycles)`. The finite Gram equations have a
solution because the actual Haar average lies in that span; conversely every
solution represents the same actual average. Its purity is recovered exactly
from those coefficients. Thus no Haar-measure or finite-moment identity remains
a caller-supplied assumption in this finite-dimensional route.

The intrinsic rank-budget projector has also been proved central in both
commuting actual matrix algebras. Every alternating operator on more than `s`
selected tensor positions annihilates that projector. This follows from actual
linear dependence of the participating tensor factors and remains valid with
additional untouched tensor factors. It supplies the necessary long-column
cutoff, but does not supply a basis or the converse classification by tableaux.

The remaining gap is now the classified spectral evaluation of these internally
constructed finite objects: the primitive central blocks and their labels, the
Weyl dimension product, the Schur--Weyl shape probability and its exponential
concentration. Merely solving each finite Gram system is not yet a proof of its
asymptotic spectrum or of the sharp support dimension.

The actual Young row and column blocks are now connected without assuming a
Schur decomposition. The occupation projector equals the finite permutation
Reynolds average. Its dimension is `choose(D+k-1,k)` and the actual flat Haar
average acts on it by

`s^(-k) choose(s+k-1,k) / choose(D+k-1,k)`.

For the column block, explicit maps from tensor coordinates to the ordinary
exterior power and back have composite `k!` times the identity. They prove the
rank of the original alternating matrix is `choose(D,k)`. Its normalized
projector is Hermitian and idempotent. The actual Haar scalar on it is

`s^(-k) choose(s,k) / choose(D,k)` (when `k ≤ D`).

The same coordinate/exterior universal property gives a complete first-column
boundary classification: at `k=s+1`, the intrinsic rank-budget space is exactly
the exterior contraction kernel. Its projector is `I - P_alt`, and its exact
rank is `D^(s+1) - choose(D,s+1)`. At `k ≤ s` the actual support is full.
These are finite-k results. They do not enumerate the growing family of Young
shapes needed for fixed intermediate s and k tending to infinity.

At rank one the literal unitary Haar average is now proved equal to the old
occupation density `symmetricState`, with no supplied ensemble identity. This
is an additional Haar connection to the previously audited pure-state object;
the new connection itself has only ordinary compilation so far.
