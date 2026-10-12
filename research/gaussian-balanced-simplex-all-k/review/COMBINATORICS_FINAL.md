# Independent internal review of the all-k Gaussian simplex manuscript

Reviewer: `conjecture_combinatorics`, 8 October 2026 (UTC).
This is an internal adversarial model review, not external mathematical peer review.

Reviewed manuscript:
`research/gaussian-balanced-simplex-all-k/paper.md`

SHA-256:
`8416f741398ceb4207edcc3ff31964883ae14044698043bf17a75d66c1dec832`.

## Conclusion and scope

I read the complete final copy and independently checked the covariance,
perimeter and radial-comparison calculations. I found no substantive
mathematical gap in the stated equal-mass theorem, including its fractional
partition extension and equality classification. This review does not
establish historical novelty or formally verify Gaussian analysis.

The claim is the equal-mass first-moment sum bound for all integers k >= 2,
with exact value a_k^2/(k-1) and attainment when d >= k-1. It does not
resolve the arbitrary prescribed-mass statement or positive-correlation
noise stability. For d < k-1 it asserts strictness for each partition,
not the fixed-dimension sharp supremum. Those distinctions are explicit.

## Checks of the argument

1. The dual infimum is finite and attained modulo constant prices:
   in the minimum-price-zero gauge it is bounded below by max(price)/k,
   and the zero-price value is finite. Pairwise ties for distinct score
   rows are Gaussian-null, so the price gradient gives balanced winning
   probabilities and hence the assignment interpretation in this case.
   The final wording correctly makes no primal-equivalence assertion at
   duplicated singular scores. Only the continuous dual value is used at
   the singular covariance boundary.

2. On the positive cone in the centered score space, score differences
   supply nonsingular affine coordinates with fixed polyhedral winning
   regions. The density and integrand derivatives are locally dominated
   by polynomial-Gaussian bounds. Every pair has a positive facet area,
   so the price Laplacian is positive on the constant-free gauge; the
   uniqueness and implicit-function steps have the required hypotheses.

3. Gaussian flux has the correct sign and normalization:
   B = L M, C = tr(LQ) = sum_{i<j} w_ij ell_ij^2, and
   tr(L) = 2 sum_{i<j} w_ij. The score covariance differential is
   dC[D] = tr(LD)/2. The covariance-path representation uses the full
   column rank of M and does not assume differentiability at a singular
   endpoint.

4. I independently read Milman--Neeman arXiv:1805.10961v3, Theorem 1.1,
   and its cluster-perimeter convention. The application is precisely
   k cells in dimension n = k-1, which satisfies k <= n+1. The cluster
   perimeter is half the sum of cell perimeters, hence sum of pairwise
   interfaces. Equal-price symmetry and unique balanced prices identify
   the equal-mass minimum with the central regular simplex. The source
   PDF retained in scratch has SHA-256
   `2bebde484903a994dcc198294e404adb4e6d20ad689cd2ba93671e6cbbae1220`.

5. The regular normalization gives L_* = c_k P and
   S_* = c_k sqrt(n/2). Weighted Cauchy--Schwarz gives
   S^2 <= tr(L) C/2, so the imported perimeter minimum implies
   C tr(L)/n >= c_k^2, with the direction and all factors correct.

6. On Q_t = Q_* + t(Q-Q_*), full rank holds for t < 1. The exact
   identity t C' = (C - tr(L)/n)/2 yields
   t h' <= h for h = C^2-c_k^2. At zero the trace-zero direction and
   regular Laplacian give C'(0)=0. Thus h/t has right limit zero and
   is nonincreasing; continuity supplies the endpoint bound. This step
   needs neither global covariance concavity nor local maximality.

7. Equality at the endpoint forces h/t identically zero. The positive
   weights then make equality in weighted Cauchy force every pairwise
   score distance equal. Centering and trace one determine Q=P/n.
   This includes a singular candidate endpoint and excludes all such
   endpoints from equality. The k=2 singleton domain is covered; k=1
   is excluded and separately treated.

8. The deficit identities (13)--(14) have the correct signs and factors.
   Integrating (h/t)'=-D/t^2 on compact subintervals and passing to the
   two endpoint limits proves convergence of the nonnegative improper
   integral. No unproved metric stability estimate is claimed.

9. For original measurable or fractional labels, each price bounds the
   feasible score average F by the dual value. Covariance homogeneity
   then gives F <= c_k sqrt(F). Equality fixes the regular Gram matrix
   and, since ties are null, forces unique winning indicators. Its rank
   is k-1, proving the lower-dimensional strictness assertion. Conversely
   flux on regular winning cells gives moments c_k v_i and attainment.

10. The exact integral a_k = k(k-1) integral phi^2 Phi^(k-2) follows
    by integration by parts with vanishing boundary terms. There is no
    numerical constant or solver assumption in the mathematical proof.

## Last-copy change

The final change to Section 2 restricts the assignment interpretation to
distinct rows. This is the clarification I requested and does not alter
the proof or the theorem. The entire new radial argument is standalone;
earlier four-cell mountain-pass, rank and Hessian arguments are historical
companions rather than dependencies of this manuscript.

## Partial Lean verification

The separate `RadialComparison.lean` has source SHA-256
`a66740074da86a0a2ea6af0f9806a3b03165d37337de4cd0807ce812fdfafa86`.
Its four proved exports formalize the abstract one-dimensional comparison,
with explicit derivative, differential-inequality and endpoint hypotheses.
Lean 4.34.1 with Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612` compiled the check-only source
successfully. `#print axioms` reports only `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`. This does not formalize Gaussian
measure, balancing prices, flux, the imported multi-bubble theorem, or
the satisfaction of the abstract hypotheses by the Gaussian value.
The parent publication workflow is responsible for fresh-source and
empty-kernel replay of the public package.
