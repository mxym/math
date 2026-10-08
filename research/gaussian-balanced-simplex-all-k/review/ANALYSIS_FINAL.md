# Independent analysis review: radial simplex comparison for every label count

Reviewer: `/root/conjecture_analysis_numbertheory`, 8 October 2026.
This record reviews the new all-k mathematical chain supplied by the root
agent. The complete manuscript and its hash will be recorded below when
available. This is internal model review, not external human peer review
and not a whole-theorem Lean certificate.

## Scope

Let k>=2, P=I-11^T/k, n=k-1, K={Q>=0,Q1=0,trQ=1}, Q*=P/n.
For uniform k-label assignments let C(Q) be the balanced Gaussian linear
assignment value. Let c*=C(Q*)=E max_{1<=i<=k} Z_i/sqrt(n), with Z_i
independent standard Gaussians. The claimed sharp partition value is
c*^2. An attaining partition requires ambient dimension at least n.
The covariance comparison itself applies to every Q in K, including
singular endpoints.

## Required differential identity and regular normalization

For Q positive on 1-perp, represent its scores by centered rows v_i of
a k-by-n matrix M with MM^T=Q. They are affinely independent. The k-1
score differences against one fixed label are an invertible affine
coordinate map. Winning sets become fixed polyhedral cones in these
coordinates. Gaussian density derivatives are locally dominated by an
integrable polynomial times a fixed Gaussian. The price Hessian is the
facet Laplacian L, positive on the common-price gauge; implicit inversion
therefore gives smooth balanced prices and C.

Every pair has a positive-area facet at every finite price vector: set
that pair's affine scores equal and all other affine scores strictly
smaller, realize these comparisons by the invertible score-difference
map, and retain the strict comparisons in an open patch of the pair
plane. This matters for the equality argument, not merely for connectedness.

Flux, with inward normals (v_i-v_j)/|v_i-v_j|, gives B=LM for the actual
moments B. Hence C=tr(LQ). The envelope derivative with
M(t)=M(I+t A)^(1/2) gives dC[D]=tr(LD)/2 for every centered symmetric
covariance direction D. The identity does not require any assumption
that scores are their own moments.

At Q*, represent the Gaussian scores as (Z_i-average Z)/sqrt(n).
Zero prices give all masses 1/k, by permutation symmetry. The unique
balanced prices in the common-price gauge are therefore zero. Every
edge length equals sqrt(2/n) and every facet weight is the same.
Thus L*=c*P, since flux gives C(Q*)=tr(L*Q*) and tr(PQ*)=1.
There are k*n/2 edges, so the regular total perimeter is

    S*=(k*n/2)(c*/k)sqrt(2/n)=c*sqrt(n/2).

All factors agree, including k=2. For k=4 this becomes the earlier
c*=sqrt(12(arctan sqrt(2))^2/pi^3), not the squared partition value.

## Imported multi-bubble theorem and the weighted inequality

I checked Milman--Neeman arXiv:1805.10961v3, printed pp2--3.
Their cluster perimeter is half the sum of cell perimeters, equivalently
the sum of ordinary interface areas for the polyhedral winning diagrams.
Theorem 1.1 covers 2<=q<=ambient_dimension+1. Taking q=k and ambient
n=k-1 is within its precise range for every k>=2. The simplicial
minimizer is central in the equal-mass case: its regular scores have
unique balanced prices modulo constants, and symmetry makes them all
equal. The uniqueness theorem is not needed.

Write w_ij=A_ij/ell_ij, where ell_ij=|v_i-v_j|. The three exact identities
are

    S=sum_{i<j} w_ij ell_ij,
    C=tr(LQ)=sum_{i<j} w_ij ell_ij^2,
    tr L=2 sum_{i<j} w_ij.

In particular, C has no extra factor two. Weighted Cauchy--Schwarz gives

    S^2 <= (tr L/2) C.

The imported perimeter lower bound is S^2>=(n/2)c*^2. Combining them gives

    C tr L/n >= c*^2.                                      (A)

No covariance stationarity, low-rank limit, price derivative, local
Hessian, numerical sign or concavity assumption is used in (A).
The underlying Q is simply full rank. All quantities are finite,
and C=tr(LQ)>0 there.

## Radial differential inequality: signs and the initial limit

Fix any endpoint Q in K and use Q_t=Q*+t(Q-Q*) for 0<=t<1.
Every such covariance is positive on 1-perp, even if Q is singular,
because its eigenvalues there are bounded below by (1-t)/n.
Since t(Q-Q*)=Q_t-Q*, the differential identity gives exactly

    t C'(t) = (C(t)-tr L(t)/n)/2.

Define h(t)=C(t)^2-c*^2. Multiplying by 2C(t) and using (A) yields

    t h'(t)=C(t)^2-C(t)tr L(t)/n <= C(t)^2-c*^2=h(t).

Thus for every 0<t<1,

    (h(t)/t)' = (t h'(t)-h(t))/t^2 <= 0.                  (B)

The sign is nonpositive, giving an upper cost bound. At t=0, h(0)=0.
Also L*=c*P, while D=Q-Q* has zero row sum and zero trace. Therefore
C'(0)=tr(L*D)/2=0, and h'(0)=0. Smoothness in a neighborhood of Q*
proves lim_{t->0+} h(t)/t=0. By (B), h(t)/t<=0, hence C(Q_t)<=c*.
Continuity of the closed-cone cost gives the same bound at t=1.
There is no derivative assumption at a singular endpoint.

## Equality and strictness

If the endpoint has C(Q)=c*, continuity gives
lim_{t->1-} h(t)/t=0. This quotient is nonincreasing and has initial
limit zero, so it is identically zero on (0,1). Thus C(t)=c*,
t h'(t)=h(t)=0, and (A) is an equality along the segment. Its derivation
was

    (n/2)c*^2 <= S^2 <= C tr L/2.

Consequently weighted Cauchy--Schwarz is an equality. All facet weights
are strictly positive at these full-rank points, so every pair edge
length is the same. A centered Gram matrix with all off-diagonal squared
distances ell^2 is Q_t=(ell^2/2)P: this follows from double-centering the
squared-distance matrix ell^2(J-I). Trace one then forces ell^2=2/n
and Q_t=Q*. For any t>0 this implies Q=Q*.

Equivalently, if Q is nonregular, every 0<t<1 has nonconstant edge
lengths and weighted Cauchy--Schwarz is strict. Thus the quotient in
(B) is strictly decreasing, and any fixed positive t gives a strict
negative margin persisting to the endpoint. Both equality arguments
avoid Milman--Neeman's uniqueness theorem.

The k=2 covariance domain is a singleton; the same conclusion holds.
For singular endpoints and k>=3, the argument likewise gives strictness.
No boundary regularity or duplicate-score exclusion is required.

## Return to measurable and fractional partitions

Let M have the actual unnormalized Gaussian moments as rows. Their sum
is zero, their Gram matrix has trace F, and their label/weighted label
is a feasible uniform assignment. For every price, pointwise winning
optimality gives F<=the dual expression. Taking its infimum yields
F<=C(MM^T). For F>0, homogeneity and the covariance result give
F<=c*sqrt(F), hence F<=c*^2. The case F=0 is strictly smaller.

Equality requires MM^T=F P/n. The row span is consequently n-dimensional
and the moment list is a centered regular simplex. Its balanced prices
are all equal by symmetry and uniqueness. Equality in the assignment
inequality means a nonnegative pointwise deficit has zero integral.
Since these full-rank regular scores have null ties, the unique winning
label is forced almost everywhere. For a fractional partition this
forces each nonwinning fractional weight to be zero and the winning
weight to be one. Orthogonal changes of coordinates give exactly the
central regular simplex fan and an unrestricted orthogonal complement.

If ambient dimension is smaller than k-1, the covariance is singular and
equality is impossible. This provides a strict, possibly non-sharp
upper bound there; it does not identify the low-dimensional optimizer.
No arbitrary-mass or positive-noise-correlation claim follows from the
uniform first-moment theorem.

## Review conclusion and limits

I found no substantive algebraic or analytic gap in this supplied all-k
chain. The regular first derivative, weighted perimeter inequality, and
radial monotonicity replace all local-Hessian and mountain-pass arguments.
The complete manuscript still needs a source-version check after writing.
This record does not establish literature priority. The imported
multi-bubble theorem and the Gaussian differential identities remain
analytic mathematical dependencies, not whole-proof Lean formalization.

## Complete-manuscript and frozen-source check

Reviewed complete source: `research/gaussian-balanced-simplex-all-k/paper.md`.
Frozen source SHA-256: `8416f741398ceb4207edcc3ff31964883ae14044698043bf17a75d66c1dec832`.

I independently read the entire final standalone paper, including its
new exact deficit identity and all-dimension/fractional formulation.
Equation (1) follows from the maximum density `k phi Phi^(k-1)` and
integration by parts; the factors k(k-1) are correct. Equation (7) has
no extraneous factor two. The regular cost and perimeter conversions in
(9), and the resulting inequality (10), match the imported theorem.
Equations (11)--(12) have the required nonpositive quotient derivative.
The derivative at zero vanishes solely because L*=c_k P and the radial
direction has zero trace. The equal-distance Gram classification in
Theorem 3 is correct, including the sum-over-j identity
`sum_j |v_i-v_j|^2=k|v_i|^2+1`.

For the deficit integral, define D as in the paper. The exact identity is
`(h/t)'=-D/t^2` on (0,1). Integrating first from a to b yields
`integral_a^b D/t^2=h(a)/a-h(b)/b`. At zero smoothness and h(0)=h'(0)=0
give h=O(t^2); at one continuity gives a finite endpoint value even for
a singular endpoint. Since D>=0, the improper integral exists, is finite,
and tends to `c_k^2-C(Q)^2`. Equation (14) is algebraically exact because
`W=tr L/2` and `S_*^2=n c_k^2/2`. Its first term is weighted edge-length
variance, and its second term is the squared-perimeter deficit. No
quantitative metric estimate is being silently claimed.

Section 2 now calls the dual value the balanced score value, asserting
assignment-optimum equivalence only for distinct score rows, which is
proved by price differentiation. This correctly avoids an unnecessary
unproved interpretation at duplicate scores. The proof at singular
endpoints uses only the dual definition and its continuity. The feasible
assignment inequality in Section 5 follows for every price and then for
the infimum, equally for fractional labels. Thus all-dimension strictness
and equality classification have complete justification.

I found no substantive mathematical gap in this final source. It is
standalone: none of the old four-cell local Hessian, rank obstructions,
facet-limit continuity or mountain-pass lemma is required. My source
verification of Milman--Neeman's dimension range and interface
normalization remains the one recorded above. This review does not
claim world priority, external human peer review, or full analytic Lean
formalization; the Gaussian multi-bubble theorem is an explicit published
mathematical dependency.
