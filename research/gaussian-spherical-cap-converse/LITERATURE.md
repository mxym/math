# Mathematical provenance and originality review

This is an **initial source screen only**. Do not describe the result
as the first proof of any dimension bound before expert literature
review and external verification.

## Direct comparator

1. OpenAI Mathematics, result family 096, *The Gaussian Propeller
   Bound in Every Dimension*, 24 September 2026:
   https://github.com/openai/math.
   General Gaussian centroid objective motivation.
2. Public independent project, arbitrary-mass Gaussian envelope:
   https://github.com/mxym/math/tree/main/research/gaussian-centroid-mass-envelope.
   Supplies sharp one-cell rearrangement and global additive 2Q(p)
   lower construction for the unrestricted high-dimensional optimum.
3. Previous project, Gaussian dimension–rate theorem:
   https://github.com/mxym/math/tree/main/research/gaussian-centroid-dimension-rate.
   Supplies an all-k constructive dimension O(log^3 k)
   upper and rate-distortion necessary dimension
   Omega(log^2 k/loglog k).

## Classical tools and closest methodological antecedents

- Marginal density of the spherical uniform measure,
  concentration of measure, spherical codes and cap-packing
  inequalities have a long literature.
- Gaussian extreme-value asymptotics and the polynomial
  Mills prefactor are classical. Both are retained in the
  present quantitative proof.
- Gamma function log-convexity follows directly from Holder's
  inequality and is standard.
- Shannon's Gaussian rate–distortion inequality underpins
  the prior entropy converse, but *not* the new spherical-cap
  strengthening.
- Wenbo Li and Qi-Man Shao, *A normal comparison inequality
  and its applications*, Probability Theory and Related Fields
  122 (2002), 494–508, DOI 10.1007/s004400100176.
  Related to Gaussian maximum comparisons and dependence,
  though this note uses a direct sphere-union argument.
- Victor Chernozhukov, Denis Chetverikov and Kengo Kato,
  *Comparison and anti-concentration bounds for maxima
  of Gaussian random vectors*, 2016.
  A related Gaussian-max comparison reference; our
  proof does not import its theorem.

## Precisely established contribution

For every sufficiently large k and every ambient dimension
d>=L^2/log L, this note proves the global finite-dimensional
defect
  k(U_k-F_d(k)) >= L^2/d-14.
Combining it with the independently verified global all-mass
envelope gives the necessary dimension Omega_C(log^2 k)
for additive C/k accuracy to the fully unrestricted
equal-mass Gaussian centroid optimum.

The improvement is **in the order of dimensional growth**,
not merely a smaller numerical constant. It is strictly
stronger than the prior project rate-distortion
Omega(log^2 k/loglog k) bound.

Open tasks include:
- a matching O(log^2 k) *sufficient* dimension construction;
- sharp constants in the finite-dimensional spherical-cap
  deficiency formula;
- uniform analogues under highly nonuniform mass constraints;
- careful novelty checking against spherical vector
  quantization, Gaussian centroid inequalities and coding
  theory, before submission.
