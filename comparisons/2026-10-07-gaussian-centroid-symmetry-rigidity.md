# Gaussian centroid dimension frontier — symmetry/variance checkpoint

*7 October 2026 PDT · strictly scoped, reproducible research progress.*

## New rigidity theorem

The global Gaussian centroid dimension programme now has a
**variance-sensitive spherical-cap bound**, independent of cell geometry.
For every equal-mass Gaussian k-partition A in R^d, put
a_i=k||integral_(A_i) x dgamma_d||, let V(A) be the empirical
variance of a_i, and write U_k for the separate one-cell
halfspace centroid ceiling. Then, for L=log k>=100
and d>=L²/log L,

\[
\boxed{k(U_k-P(A))+V(A)\ge 2L^2/d-28.}
\]

At dimensions d/L²->c>0, the exact asymptotic coefficient is

\[
\liminf \{k(U_k-P(A))+V(A)\}\ge2/c.
\]

The previous general-partition converse had coefficient 1/c,
so **homogeneous-centroid (V=0) candidates have a strictly
stronger obstruction**.

For additive C/k accuracy relative to the unrestricted
global optimum F_infty(k), the simplex/Gumbel comparator gives

\[
\liminf V(A)\ge
\max\{0,2/c-C-2(1-\gamma)\}.
\]

If the right side is positive, a fraction of order
1/log k of all cells must display constant-scale
conditional centroid norm deviations. Equivariant/transitive
Gaussian partitions have V=0 and cannot beat this
asymptotic barrier.

## Public research artifacts

- [Analytic proofs](../research/gaussian-centroid-symmetry-rigidity/paper.md)
- [Lean 4 binary character and full signed-energy isometry kernel proof](../research/gaussian-centroid-symmetry-rigidity/formal/GaussianCodeCore.lean)
- [Lean axiom/scope audit](../research/gaussian-centroid-symmetry-rigidity/formal/LEAN_AUDIT.md)
- [Reproducible exact rational checker](../research/gaussian-centroid-symmetry-rigidity/check_exact.py)
- [Source provenance](../research/gaussian-centroid-symmetry-rigidity/LITERATURE.md)

The standalone Lean 4.34.1 module imports only Init.
Kernel check has succeeded. It formalizes **only finite
binary group/algebraic isometry identities**, not
the Gaussian cap theorem itself. The analytic and
finite checker scopes are stated separately.

Previous prerequisites:
[all-mass Gaussian envelope](../research/gaussian-centroid-mass-envelope/README.md),
[spherical-cap converse](../research/gaussian-spherical-cap-converse/README.md),
[sharp-constant dimension-rate](../research/gaussian-sharp-dimension-rate/README.md).

## Remaining genuine core question

It is not known whether the sharp
dimension-constrained global optimizer is
homogeneous in conditional centroid norm.
In fact one-dimensional equal-mass interval
partitions can be inhomogeneous; equal mass alone
does not imply equal centroid norm. Resolving
the actual optimizer's norm variance at
d~c(log k)^2 is necessary before upgrading
the generic 1/c dimensional obstruction to
the transitive 2/c coefficient.
The finite-k Standard Simplex global
optimality problem is not resolved.
