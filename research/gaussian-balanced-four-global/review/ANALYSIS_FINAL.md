# Independent analysis-agent review of the covariance-deformation proof

Reviewer: `/root/conjecture_analysis_numbertheory`, 8 October 2026.
Reviewed source: `research/gaussian-balanced-four-global/paper.md`.
Reviewed source SHA-256: a88704330cefdb377e56a209d3105f2740ad4776fd8b25b3687aab7465475244.

This is an internal model review, not external human peer review and not a
formal proof certificate. I read the complete standalone manuscript, checked
the old local/rank-two calculations against their earlier full version, and
recomputed the main finite algebra directly. No floating experiment is used
in the conclusions below. I did not verify every argument in the published
Gaussian isoperimetric theorems from first principles. Their precise scope
and normalization were checked against Milman--Neeman's original text.

## Overall finding and remaining verification limits

I found no substantive mathematical gap in the reviewed proof. In particular,
the smooth regularization fixes the original nonsmooth-boundary objection:
no differentiability of the unregularized covariance function at duplicate
scores is used. The critical-point separation argument excludes such limits
before the facet-continuity argument is invoked. The upper-normal sign in
the constrained mountain-pass lemma is correct and supplies exactly the
spectral inequality needed for the low-rank obstruction.

This conclusion does not assert historical originality, peer review, or a
Lean formalization of Gaussian analysis. The imported multi-bubble theorem,
ODE existence/continuous dependence, and analytic variation arguments remain
written-mathematics dependencies. The assertions below describe the actual
checks rather than treating agreement between models as a premise.

## Assignment value and all degeneracies (Sections 2 and 10)

* The gauge `min lambda = 0` is coercive: a zero-priced label gives an
  expected maximum at least zero; the price average is at least
  `max lambda / 4`. Thus the stated minimum exists, including repeated
  scores. The nonnegative value also follows directly by bounding the
  maximum by the average of the four scores.
* With distinct score rows, each tie has Gaussian measure zero even at
  rank one or two. Differentiation in the prices therefore gives all four
  quarter quotas. For any feasible fractional assignment, its pointwise
  weighted score is at most the winning score, so its linear value is at
  most the price expression and hence at most its infimum.
* The coupling interpretation at repeated scores has a complete compactness
  justification: realize approximating scores on one Gaussian space;
  indicator assignments lie in the weakly compact closed convex subset of
  four copies of L2 given by positivity, the upper bound one, unit sum,
  and the quota equalities. Scores converge strongly in L2. Thus their
  pairing with the weakly convergent assignments tends to the limiting
  optimum. A fractional assignment represents a conditional probability
  kernel for the label and supplies a coupling. Continuity of the dual
  values is Lemma 2, independent of this compactness argument.
* In the final inequality, no attainment or geometric structure of the
  original partition is needed: for every price, its feasible labels give
  `F <= price expression`, so `F <= C(M M^T)`. For `F > 0`, divide the
  covariance by F and use degree-one-half homogeneity. For F=0 the claim
  follows separately.
* Equality forces the normalized covariance to be P/3. A full-rank regular
  diagram has unique balanced prices modulo constants; by symmetry those
  constants are the only price vector. Zero pointwise assignment deficit
  then forces every fractional assignment to be the unique winning label
  almost everywhere. This proves the fractional as well as measurable
  equality classification. Extra ambient coordinates do not change the
  Gaussian score law and remain unrestricted.

## Smooth interior score/price calculus (Section 2)

The full-rank three score differences give an invertible coordinate map.
After incorporating their price shifts, all four winning sets are fixed
polyhedral cones. In any compact parameter neighborhood of an invertible
map, derivatives of the changed Gaussian density are bounded by an
integrable polynomial times a Gaussian with a fixed positive decay rate.
This justifies the differentiations asserted in Lemma 3.

Every pair has a positive-area facet for every finite price vector: assign
its two affine scores equal values and the other two strictly smaller
values; affine independence lets these three score differences be realized
at a point in R3, and the strict comparisons persist on a relatively open
patch of the pair plane. Hence the price Hessian L is strictly positive on
the price gauge. Its positivity holds throughout any price segment, so the
claimed uniqueness and implicit-function inversion are valid.

The Gaussian flux sign is correct: the inward normal is the positive
score-difference direction. The envelope derivative in score coordinates is
its cell-moment matrix B. With `M(t)=M(I+t A)^(1/2)`, differentiation gives
`dC[D]=tr(B^T M A)/2=tr(LD)/2`. This identity is on the full six-dimensional
centered symmetric space; the trace-affine tangent is its trace-zero part.

## Pair separation and boundary facet continuity (Sections 3--4)

The pair union D need not be convex. On that union the labels are separated
exactly by their pairwise score hyperplane. Its projected subdensity has
mass one-half and is bounded by phi(0). Each side has mass one-quarter.
Layer cake therefore gives

    integral |z-t| g(z) dz >= integral_0^(1/(4 phi(0)))
                              (1/2 - 2 phi(0) s) ds
                            = 1/(16 phi(0)).

The subtraction of t is legitimate precisely because the two masses are
equal. No maximization of squared moments is used. The two pairwise winning
halfspaces separately have mass at least one-quarter, which yields
`-q <= (lambda_i-lambda_j)/|v_i-v_j| <= q` with q=Phi^-1(3/4).

For facet continuity, select a continuous local orthogonal frame on the
plane normal's sphere chart. Restrictions of the other affine comparisons
then converge in fixed two-dimensional Gaussian coordinates. A nonconstant
limiting comparison has a null zero set. A constant nonzero comparison is
stable. A zero constant comparison is a codimension-one triple tie. The
three distinct score vectors and matching prices would then be affinely
collinear; their middle affine score is a strict convex combination of the
outer scores everywhere, making its cell null. Positive quarter mass
excludes this case. Dominated convergence therefore applies to every facet,
including absent limiting facets. Denominators stay positive by separation.
The same Gaussian dominated convergence applies to first moments, or the
limiting flux identity gives the same actual moment matrix directly.

## Complete low-rank obstruction (Section 5)

The three-cell bound uses an unrestricted assignment, so identical inducing
scores may simply give an empty label; no quota is being silently imposed
on that intermediate sector partition. In a plane, a sector's moment norm
is `sin(alpha/2)/sqrt(2 pi)`, from its elementary angular/radial Gaussian
integral. The identity `sum sin^2 x_i = 2 + 2 product cos x_i`, with sum
x_i=pi, gives the stated 9/(8pi) bound. If a cosine is negative, at most one
is, so the product is nonpositive; otherwise concavity of log cos applies.
Endpoints and rank-one degeneracies are harmless.

The profile estimate is strictly and exactly justified: `pi < 32/9` gives
`phi(0)>3/8`; integration of `1-x^2/2` to 3/4 gives 87/128, hence
q<3/4. The exponential Taylor lower bound at 9/16 is 4637/8192, strictly
larger than 9/16. Thus both `h0^2>B3/4` and `h0>3 phi(0)/4` follow. This
uses no numerical approximation to q.

In rank two, the kernel of the PSD matrix W=P-L contains the constant
vector and two independent moment columns. Its remaining dimension is one,
so W=c a a^T, c>=0. For a genuine convex quadrilateral the alternating
sign dependence is nonzero at all four vertices; the two diagonal facets
require opposite signs of the same constant price combination, while both
must have positive weights. If a point lies in the other three points'
hull, `w_4j<=1/4` follows even with zero hull coefficients. Merging an
appropriate pair yields `F+2t^2<=B3`; projection yields `F>=4t^2`; together
these give `F+4t^2<=4B3/3`. The fourth-cell isoperimetric perimeter bound
then contradicts the strict profile estimate. These cases exhaust four
distinct rank-two points. None of these steps assumes global maximality.

For rank one, increasing scores give the four quantile intervals. Their
actual moments are exactly the four stated values. The middle score gap is
`2(phi(0)-h0)>0` and its facet area is phi(0), so its weight is greater
than two. Accordingly `tr L >= 2 w_23 > 4`, incompatible with `L<=P`
and `tr P=3`. This is stronger than merely comparing a rank-one objective
with another partition, and applies to the limiting critical points.

## Regular strict local maximum (Section 6)

The regular facet area is `phi(0) theta/pi`; its edge length is
`2 sqrt(2) a`, giving weight one-quarter exactly when
`a=theta/pi^(3/2)`. Consequently the actual moments equal `a sigma_i`
and the regular assignment/covariance conversions give `c*=sqrt(F*)`.

I checked the first-order mass and facet-weight formulas directly. The
facet conditional mean is `h e_x`, where
`h=sqrt(pi/3)/theta`. Summing mass flux yields exactly
`delta p_i=a sigma_i dot (h(b_x,b_y,b_z)-z)`.
For the b_x perturbation the 12 plane stays y+z=0, while its wedge becomes
`X >= (1-b_x)|Y|/sqrt(2)` to first order. Its angle derivative is
`sqrt(2)b_x/3`, and its edge length has relative derivative b_x. The
opposite facet has the opposite signs. Apex translation gives the negative
conditional-mean dot z contribution. These confirm formula (15).

For an independent Hessian expansion put
`d=c0-1-h^2`. The two x-pair contributions to `H''` are

    4 a^2 K_x(v+s) + 8 a^2 d b_x^2.

Adding cyclic pairs, use

    sum K_x(v+s) = ((c0-1)(u+v+s)^2
                    -(3c0+1)(u^2+v^2+s^2))/2.

Writing u,v,s=rho+(u0,v0,s0) gives precisely (16). The coefficient signs
are strictly negative because `theta>sqrt(2)/3` and h is real. Polar
rotation removal parametrizes all nearby centered full-rank score lists,
not merely a special deformation class. Restricting to the trace-one
covariance normalization removes the norm term of H and preserves strict
local maximality for C.

## Multi-bubble input and constants (Section 7)

Read original source: Milman--Neeman arXiv:1805.10961v3, 30 Nov 2021.
Its printed p2 defines cluster perimeter as half the sum of cell
perimeters; printed p3 Theorem 1.1 covers 2<=q<=n+1. Here n=3 and q=4,
so the hypothesis is exactly satisfied. Polyhedral winning cells have
finite Gaussian perimeter, and their interface sum is this same
normalization. The uniqueness theorem is not required.

Independently, the regular self-moment edge length is `2 sqrt(2) a` and
weight is 1/4, so `S*=3 sqrt(2) a=c*sqrt(3/2)`. For an interior critical
point, L=mu P, C=mu and each edge weight is mu/4. Centering and trace one
give `sum edge_length^2=4`. Cauchy--Schwarz bounds the perimeter above by
`mu sqrt(3/2)`, while multi-bubble bounds it below by the regular value.
Thus the critical-value inequality has the stated lower direction.

## Mountain-pass normal sign and regularization (Sections 8--9)

For p=Pi_K(x+grad f) and D=p-x, the projection inequality tested at x
is `grad f dot D >= |D|^2`, and D=0 is precisely the upper-normal
condition. The compact near-critical strip has a positive uniform lower
bound for |D| if the critical level has no zero. The cutoff flow is
locally Lipschitz; for step size h<=1, each forward Euler iterate is the
convex combination `(1-h chi)x+h chi p`, hence stays in K. Standard ODE
convergence preserves invariance and gives continuous dependence. The
cutoff fixes both high-valued endpoints. A near-optimal path has minimum
above b-eta/2; the flow raises each lower point past b+eta/2 in uniform
time at most eta/alpha^2, contradicting the defining supremum. This proves
the required sign even on a singular PSD boundary; it is not the usual
unconstrained critical-point statement imported without boundary checks.

For fixed epsilon>0 the regularized argument has eigenvalues at least
epsilon/3 on 1-perp. Thus C_epsilon is smooth on an actual open neighborhood
of K. Uniform convergence follows from continuity and compactness.
The strict local maximum supplies the uniform barrier, with both endpoints
strictly above it; this applies even if the other maximizer has equal value.

The top-eigenvalue variational principle gives (20), including the range
condition. No covariance-gradient sign is reversed. With A=L-mu P,

    ||B-mu M||_F^2 = tr(A^2 ((1-eps)Q+eps P/3))
                   = eps tr(A^2)/3.

All three eigenvalues of L lie between zero and mu. Hence the residual is
at most eps mu^2. Euler's identity gives
`C(tilde Q)=(1-eps)mu+eps tr L/3`, and the moment norm bound gives
`0<mu<=2h0/(1-eps)`. A difference of two residual rows is bounded by
sqrt(2) times the Frobenius norm. Combining this with pair separation
therefore yields exactly (22), a uniform positive separation as eps->0,
and a positive lower bound for mu. This closes the coincident-score
objection without taking any derivative there.

Bounded pairwise prices, compact covariance factors and Lemma 5 then give
a balanced noncoincident limiting diagram with `B0=mu0 M0` and
`L0<=mu0 P`. Rescaling both scores and prices by positive mu0 changes no
cells, makes the scores their own moments, and divides their facet matrix
by mu0. Lemma 6 excludes rank at most two. Full rank forces L0=mu0 P and
Lemma 8 contradicts the strict subregular barrier. Every equality and
scaling conversion in this step is consistent.

## Source scope and interpretation

I also checked Heilman arXiv:1211.7138v2, printed pp9--10
(Definition 2.2 and psi_0) and p37 (Conjecture 3): its feasible class is
indeed the equal-quota fractional class, and its objective is the sum of
squared first moments. The present stronger regular classification implies
its stated simplicial-conical conclusion. In arXiv:1901.03934v1, printed
p8, Problem 1.15 and Conjecture 1.16 reduce to the same first-moment
optimization at equal masses, up to constant terms/factors. No positive
noise-correlation or arbitrary-mass theorem follows merely from this result.

## Final editorial-version check

The reviewed final manuscript SHA-256 is `f86af0ff6f1eb32a8f7fbdb8105aa0a5c4b4d82e6cd307ea1b167a7bc0cb9d24`.
Relative to the earlier version, I checked the explicit halfspace bound
`(T-q)(f-1_{T>=q})<=0`, the first-moment dominated-convergence sentence,
and the equal-mass central-price argument in the multi-bubble bridge. All
three additions are correct and introduce no new mathematical premise.
Display-delimiter changes for PDF rendering likewise do not change the
mathematics. The review conclusions above apply to this version.

## Matrix-square notation check

Frozen-source SHA-256: `570518f50ff0c656fb52cd9d7fdcb59d19fcfbd24260d180c5d2b4b28ea0e70d`. Equation (21) now writes
`tr[(L-mu P)^2]` with explicit brackets, matching the trace of the matrix
square used throughout the reviewed algebra. I checked this display; it
introduces no mathematical change and resolves possible reading as the
square of a trace. The preceding conclusions apply to this source.
