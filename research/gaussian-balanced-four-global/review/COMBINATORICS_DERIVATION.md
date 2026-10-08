# Independent internal review of the regularized mountain-pass proof

8 October 2026. Reviewer: the combinatorics research agent. This is an
internal derivation check, not external expert review and not a whole-proof
Lean certificate. The reviewed draft was `/workspace/scratch/gaussian-mountain-pass/PROOF.md`.
No numerical evidence was used for the main implication.

## Main chain

The sign in the compact-convex mountain-pass condition is correct.
For a smooth function f and compact convex K, set
D(x)=projection_K(x+gradient f(x))-x. Projection optimality gives
gradient f(x) dot D(x) >= |D(x)|^2. Also D(x)=0 exactly when
gradient f(x) is an upper normal to K. A nonnegative cutoff of the
Lipschitz vector field D preserves K: forward Euler steps of sufficiently
small size are convex combinations of x and its projection. On a compact
critical-free value strip its squared norm is bounded below, giving the
usual path-raising contradiction. Thus the required critical point has
an upper normal, including on singular PSD faces.

For K={Q PSD on 1-perp, trace Q=1}, maximizing trace(LQ) gives the
normal-cone conditions L<=mu P and (L-mu P)Q=0. For the regularized
Qtilde=(1-epsilon)Q+epsilon P/3, Gaussian flux and homogeneity give
C(Qtilde)=(1-epsilon)mu+epsilon trace(L)/3. Thus
C(Qtilde)<=mu<=C(Qtilde)/(1-epsilon).
Writing B=LM and MM^T=Qtilde, the residual is exactly
|B-mu M|_F^2=(epsilon/3)trace((L-mu P)^2)<=epsilon mu^2.
All three eigenvalues of L on 1-perp lie in [0,mu]; no solver assumption
is involved.

For any two balanced winning cells, their union D has Gaussian mass 1/2
and the score-gap direction divides it at a median. Its one-dimensional
subdensity is bounded by phi(0). The projected moment difference is
at least (1/2)^2/(4 phi(0))=1/(16 phi(0)). This uses only the winning
rule and equal cell masses, and does not require moment-objective
optimality. Together with the residual and mu's uniform bound, it
excludes every repeated-score limit.

## Boundary continuity

Bounded prices follow from the two quarter-mass pairwise winning
halfspaces: the normalized price gap lies in [-q,q], q=Phi^-1(3/4).
On a pair's facet choose a continuously varying orthonormal frame.
The two remaining inequalities have coefficients continuous in scores
and prices. A nonzero limiting affine inequality has a Gaussian-null
zero set on the plane. A zero linear coefficient with nonzero constant
has a stable indicator. The sole problematic zero/zero case is a
codimension-one triple tie. Three distinct collinear scores with affine
prices have one score globally between the other two; its winning cell
has measure zero. Four positive quarter masses exclude this case.
Consequently dominated convergence gives both cell masses and facet
areas, and pair separation protects the weights' denominators.

## Old inputs rechecked

The rank-two obstruction uses only own-moment stationarity, L<=P,
quarter masses, the classical unrestricted three-cell moment bound,
and single-cell Gaussian isoperimetry after the spectral constraint is
obtained. In particular it does not subsequently use global maximality.
The convex-hull case includes zero barycentric coefficients. The four
extreme-point case forces both diagonals to have positive weight, whereas
the Radon dependence permits at most one of their ordinary facets.

For rank one, own moments are (-h,h-h0,h0-h,h), h=phi(q), h0=phi(0).
The middle facet has weight h0/(2(h0-h)). The existing exact profile
bound h>3h0/4 makes this weight greater than 2, so trace L>4>3,
contrary to L<=P. An even weaker h/h0>23/32 from q<3/4 suffices.

For the old local Hessian, the diagonal contribution is
4 a^2 sum_x K_x(v+s). Decomposition into scale rho and trace-zero
coordinates yields -24a^2rho^2-2a^2(3c0+1)sum u0^2.
For an off-diagonal b_x variation, the opposite edge products
(delta d) dot d are +/-8a^2 b_x and the corresponding weight changes
are +/-(c0-1-h^2)b_x/4, giving
-8a^2(1+h^2-c0)b_x^2. The two remaining pairs are cyclic copies.
The local facet wedge has slope (1-b_x)/sqrt(2), yielding the stated
angular derivative sqrt(2)/3. This independently recovers the signs
and factors needed for the strict local maximum on covariance space.

## Imported perimeter theorem

The original Milman--Neeman arXiv:1805.10961v3 was read. Its Theorem 1.1
covers q=4 cells in dimension n=3, and its cluster perimeter is one half
the sum of individual perimeters, exactly sum A_ij here. For the
trace-one regular fan, edge length sqrt(2/3) and
A_ij=phi(0) atan(sqrt(2))/pi give w_ij=c*/4 and
S*=c*sqrt(3/2). The critical-value inequality has the correct direction:
S>=S* and S<=C(Q)*sqrt(3/2) imply C(Q)>=c*.

No substantive gap was found in the reviewed chain. The formal manuscript
should restate the old rank-two lemma with its actual stationarity and
spectral hypotheses, rather than leave a nominal global-maximizer
hypothesis that would require readers to reconstruct this audit.
