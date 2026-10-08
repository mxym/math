# Historical provenance: Gaussian widths and symmetry obstructions

Preliminary originality screen; no world-first claim.

## Inputs to the variance-rigidity theorem

1. The all-mass Gaussian first-moment envelope:
   https://github.com/mxym/math/tree/main/research/gaussian-centroid-mass-envelope
   establishes the scalar sharp halfspace bound and
   fixed-mass dimension-stabilization framework.

2. The spherical-cap Gaussian dimension converse:
   https://github.com/mxym/math/tree/main/research/gaussian-spherical-cap-converse
   establishes the exact finite spherical maximum
   envelope and its 2L²/d dimensional curvature term.

3. The sharp-constant Gaussian dimension–rate result:
   https://github.com/mxym/math/tree/main/research/gaussian-sharp-dimension-rate
   gives the Gumbel comparator
   k(U_k-F_infty(k)) <=2(1-gamma)+o(1)
   and the precise constant-order cap expansion.

4. Kabluchko, Litvak and Zaporozhets,
   *Mean width of regular polytopes and expected maxima
   of correlated Gaussian variables*,
   Journal of Mathematical Sciences 225 (2017), 770–787:
   https://arxiv.org/abs/1511.08479 .
   Gaussian maxima, regular simplex mean width and
   asymptotic Gumbel behavior have classical
   precedent; our note does not claim
   those Gaussian-max facts as original.

5. Orthogonal Gaussian invariance, finite-dimensional
   conditional centroid covariance, and
   transitive finite group actions are classical.

## Precisely claimed contribution

The derived exact identity
 k(U_k-P)+V=h_k²-(mean conditional centroid length)²
connects sphere-width bounds directly to the
variance of Gaussian conditional centroid norms.

The resulting nonasymptotic inequality
 k(U_k-P)+V>=2L²/d-28
and the asymptotic 2/c inequality isolate
a **quantitative symmetry-breaking penalty**
for any nearly optimal equal-mass Gaussian
partition at quadratic-logarithmic dimension.
This is a more structured theorem than the
previous general 1/c bound, but is conditional
on the already known spherical-cap ingredients.

A standalone Lean source formalizes only the
Boolean-character algebra behind transitive
binary code actions, not the whole Gaussian
probability argument.

Historical equivalence to known Gaussian
quantization stability theorems remains
unverified; specialist review is needed.

## Open issues not resolved

- Sharp leading dimension coefficient in the
  unrestricted Gaussian partition optimum.
- Necessity or impossibility of actual
  symmetry breaking in fixed-dimensional
  extremizers.
- Exact optimizer and uniqueness for
  finite k>=4 equal-mass Gaussian partitions.
- Full Lean formalization of Gaussian
  extrema and cap probability inequalities.
