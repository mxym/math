# Ordinary proof check and remaining connection

The manuscript's flat-average argument is mathematically consistent for fixed
`D` and `1 ≤ s < D`. The degree is `g = s(D-s)`, and the constant is

`c = s^(-g) / product_(i<s,j<D-s) (s+j-i)`

with zero-based indices. The shifts are all positive. The new Lean product uses
exactly these shifts. The actual coordinate Haar average and its exact support
are now derived internally, including singular densities and blocklength zero.

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
