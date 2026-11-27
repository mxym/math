# An optimal affine-restriction decomposition for fixed-degree binary polynomial sources

This supplement addresses the first structural question in Section 11
of Chandrasekaran–Goodman–Zuckerman, *Quadratic Extractors*. It is
separate from the earlier self-contained cubic-only bound and does
not change that result.

For every fixed d >= 2 and integer m >= 8d, there is a dimension
threshold L(d,m) = O_d(m^d). If f has Boolean degree at most d and at
least L(d,m) generating bits, there is an m-dimensional direction
space W such that, simultaneously on all cosets of W, either

- the restriction has degree at most d-1; or
- every (d-1)-fold derivative along a linearly independent direction
  tuple has min-entropy at least floor(m/2) on the restriction.

The two alternatives are for one common W. An injective generator
gives an exact equal-weight mixture with component min-entropy m.
For an arbitrary generator of output min-entropy at least
L(d,m) + m + log2(1/epsilon), discard at most epsilon total mass of
noninjective cosets to obtain the same kind of mixture within epsilon
in total variation. This makes m = Omega_d(k^(1/d)) for fixed error.

A counting construction shows that the exponent 1/d is sharp for
this affine-restriction formulation with derivative threshold
floor(m/2), already for injective generators. It is not an
obstruction to arbitrary reparametrisations of a distribution.
Dependent directions are necessarily excluded: over F_2 they give
identically zero derivatives.

The proof uses the dense-multilinear-variety theorem of Milićević;
an explicit binary version of that dependency is proved in the
appendix, with attribution. We claim no efficient discovery
algorithm, disperser, extractor, tensor rank combiner, or
deployment-security result.

See PROOF.md, SOURCES.md, and RESULTS.txt. To run the deterministic
standard-library checks:

    bash replay.sh
