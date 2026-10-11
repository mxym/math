# Remaining mathematical obligations — partial formalization

The global sharp four-cell inequality and complete equality classification are
not exported. No item below is supplied as an axiom or hidden assumption of a
purported main theorem. This report distinguishes actual checked constructions
from the still-missing global analysis.

## What is now constructed

The owned import closure includes the actual standard Gaussian measure,
measurable fractional labels, Bochner first moments, balancing prices, price
duality and its fractional equality condition. The `analytic/` sources listed
in `UPSTREAM_PROVENANCE.json` are integrated by source, not by assuming their
conclusions. Covariance value is factorization-independent, has the proved
scaling law, and is continuous on the PSD cone, including singular points.

`actual_centered_covariance_fixed_differential` constructs one positive
symmetric Gaussian flux family **before** quantifying over all centered
symmetric directions D. Its exact statement is the one-dimensional derivative
of t -> covarianceValue(Q+tD) at zero, equal to trace(L D)/2. It is not yet a
Frechet-smoothness theorem for the covariance value on its positive cone.

`actual_four_local_extremum_self_moments` constructs actual balanced cells and
Bochner moments at a full-rank constrained local extremum. It proves C(Q)>0,
m_i=C(Q)r_i, and L=C(Q)P with actual canonical prices. It does not prove that
such an extremum is tetrahedral, nor bound its value by the sharp constant.

`actual_simplicial_price_hessian` gives the actual second Frechet derivative
of the original price objective, with a positive Gaussian flux matrix and
exact constant-shift kernel. `actual_simplicial_price_hessian_nondegenerate`
additionally proves that its restriction to sum-zero prices is bijective.
These hold for affine-independent d+2 scores in R^(d+1); the four-cell case is
the intrinsic R^3 case. They do not silently extend to degenerate diagrams.

## 1. Higher regularity and the two different Hessians

Prove the covariance value has the regularity needed by the manuscript's
regularized deformation and local second-variation arguments on the positive
centered cone. A fixed directional derivative formula does not supply this
regularity. The price Hessian is now proved, but its continuity in joint
score/price parameters and the resulting smooth implicit dependence of
normalized prices still require proof. Centered invertibility alone does not
establish an implicit-function theorem's other hypotheses.

Derive the **covariance** Hessian at the regular tetrahedral covariance and
formula (16), including all derivatives of the balancing prices. Then prove
strict local maximality. This is distinct from positivity of the price
Hessian; the two must not be conflated.

## 2. Singular convergence and actual facet geometry

The six-module facet-chart extension now proves joint continuity of actual
Gaussian chart integrals at positive-mass diagrams, including singular limits,
and identifies their weights with the existing epigraph flux coefficients.
Fixed orthogonal charts are constructed rather than assumed to vary smoothly.
See FACET_PROGRESS.md. Coordinate-independent surface/perimeter identification,
chart compatibility and the complete arbitrary-cell limiting flux argument
remain; the following global obligations are not discharged by local chart
continuity alone.

The exact pair-price bound, centered-price compactness, moment separation,
non-coalescence and positive-mass collinear triple-tie obstruction are proved.
Continuity of Bochner winning moments is proved at distinct score families;
price differentiability of actual cell masses is proved for affine-independent
simplicial scores. The missing boundary work includes limiting mass constraints
and convergence of moving-hyperplane Gaussian
facet integrals, including disappearing facets, collinear triples and
rank-deficient limiting configurations.

Identify the flux coefficients with the exact geometric surface quantities
used by the Gaussian perimeter inputs. Construct the required local frames,
prove their continuous dependence, justify all dominated-convergence limits,
and preserve the flux identity and spectral bounds in the singular limit.

## 3. Spectral transport, regularized limits, rank-one and rank-two exclusion

Upper-normal equivalence and full complementary slackness are proved for
arbitrary finite real PSD trace-one matrices. The exact residual identity and
bound are proved in intrinsic three-dimensional coordinates. Complete their
application to the constructed regularized covariance objectives, including
coordinate transport, limiting critical sequences, and self-moment rescaling.
A full-rank local-extremum theorem is not a theorem about every such singular
limit.

For rank one, an ordered collinear self-moment diagram already contradicts the
explicit adjacent-facet quadratic-form bound, in every ambient dimension by
actual Gaussian projection and Bochner transport. Still derive that ordered
representation from an arbitrary rank-one covariance limit, with relabeling,
and identify its actual facet form with the limiting normal-cone matrix.

For rank two, prove the complete affine-dependence and planar hull case
analysis of Lemma 6 for four distinct centered actual self-moment scores,
including absent interfaces and collinear triples. Establish violation of
the actual inequality L<=P in every case.

## 4. Genuine geometric lower bounds

The proved one-cell **moment** bound and strict quarter-quantile margins are
not Gaussian **perimeter** isoperimetry. Prove the latter for the actual
perimeter and all sets required by the planar argument. Also establish the
unrestricted three-cell first-moment bound 9/(8*pi) in the merged-cell setting;
an equal-mass three-cell theorem alone does not cover unequal merged masses.

Prove the four-cell equal-mass Gaussian perimeter minimum in d>=3 with the
normalization P_gamma=(1/2)sum_i Per_gamma(C_i), plus its required rigidity.
This is the manuscript's Milman-Neeman input. Its published proof has not
been formalized in this import closure. Neither it nor single-cell
isoperimetry is introduced as a custom axiom.

## 5. Tetrahedral analytic constant and constrained mountain pass

Compute the actual centered tetrahedral Gaussian Bochner moments and evaluate
the analytic angle integral, obtaining exactly
12*(arctan(sqrt(2)))^2/pi^3. Generic regular-simplex values or finite algebraic
identities do not replace this evaluation.

Construct the constraint-preserving continuous deformation/flow with the
upper-normal sign on compact positive trace slices. Prove existence,
quantitative ascent, the minimax argument, regularization control and passage
to the singular boundary. Assemble the global exclusion with the actual
critical-value perimeter lower bound. No flow or deformation is postulated.

## 6. Final arbitrary objects and full equality classification

Prove the sharp global covariance comparison, then transfer it to every
measurable four-cell partition and every measurable fractional partition
with actual masses 1/4. Establish all dimension and almost-everywhere details.

Prove both directions of equality: after a permutation and an orthogonal
transformation/isometric embedding of R^3 into R^d, the labels are a.e. the
centered regular tetrahedral winning-cone indicators with unrestricted
orthogonal-complement coordinates; conversely every such cylindrical
partition attains the exact constant. Existing fractional dual equality does
not prove the missing tetrahedral covariance rigidity.

These are mathematical gaps, not remaining packaging tasks. The exact
verified declarations are enumerated in ROOTS.txt and source-bound receipts.
