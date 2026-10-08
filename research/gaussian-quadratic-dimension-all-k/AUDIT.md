# Analytical proof audit: all-integer Gaussian dimension theorem

**Self-audit status.** This is a complete classical-probability
argument, not a formal kernel-checked proof or independent human
peer review. The only non-elementary input is a standard
Berry–Esseen theorem; the exact external statement is quoted
in paper.md and referenced in LITERATURE.md.

## Logical dependencies and scope

1. The theorem concerns k=2^r for all sufficiently large r.
   The explicit sufficient logarithmic threshold L>=10^10
   is intentionally conservative. It provides a concrete
   absolute r_0. No finite small-r universality is asserted.
2. A full-rank binary generator gives **k distinct**
   unit score vectors. A transitive orthogonal sign-flip
   group permutes all score-maximizing cells; null tie
   hyperplanes ensure exact masses 1/k.
3. Every two distinct nonzero vectors in F_2^r are
   independent as linear functionals. For each independent
   random column, the pair of their character signs
   is uniformly distributed over four pairs. This makes
   their full weighted score sums pairwise independent
   conditional on the Gaussian data vector.
4. Applying Chebyshev to a sum of pairwise independent
   exceedance indicators gives failure probability
   1/[(k-1)q], with no assumption of joint independence
   among three or more message scores.
5. The good Gaussian event is expressed using Q2 and Q4.
   Normal moments 1,3,105 give exact mean and variance
   identities, and P(good complement)<=10/m.
6. The exponential tilt factorization is exact for
   nonidentical, possibly signed, coefficients a_j.
   Every tilted summand has variance
   a_j^2 sech^2(lambda a_j). Lower bound V>=1/4
   uses the inequality sech^2(x)>=1-x^2.
7. For local interval mass, Berry–Esseen is used in
   the **general independent, nonidentical** form,
   not just the i.i.d. specialization. The ratio
   of total third absolute moments to V^(3/2)
   is bounded by 64 sqrt(20/m).
8. Because the interval width is 1/lambda and
   lambda<=2 sqrt L, its Gaussian mass is >=1/(10lambda).
   At L>=10^10, twice the Berry–Esseen error
   is <=1/(20lambda). Thus a strictly positive
   local tilted interval is rigorously obtained.
9. The crucial entropy identity
   log cosh(x)-x tanh(x)+x^2/2>=0
   is established by differentiating an even function.
   This gives the exact lower exponent -L, independent
   of the Gaussian realization's random Q2.
10. Thresholds depend measurably on Gaussian data,
    but the pairwise-independent Chernoff/second-moment
    argument is always performed **conditional on the
    entire data vector**. Thus there is no illicit
    use of unconditional pairwise independence.
11. The y-dependent failure estimate is integrated.
    A one-point exceedance probability would only yield
    an O(1) expected-score error, insufficient to prove
    an O(1/k) squared-centroid gap. The integrated proof
    controls the necessary O(1/sqrt L) error.
12. On the Gaussian bad event, the maximum is bounded
    below by the zero-message score X0; Cauchy–Schwarz
    costs at most sqrt(10/m). No silent truncation of
    Gaussian tails occurs.
13. Rank failure has probability at most
    k*2^(-m). A Gaussian union bound gives
    E M^2 <=2L+3, enabling removal of all deficient
    generators at cost <=2/sqrt L, without changing
    the analytic conclusion.
14. The average over full-rank generators is positive,
    so some deterministic full-rank matrix achieves it.
    This is an existence result, **not** a polynomial-time
    algorithm to find the matrix.
15. The squared-score objective lower bound uses
    Cauchy–Schwarz and unit score-vector norms. A
    separately proved Mills upper quantile estimate
    h_k^2<=2L-log L+3 gives the additive 100/k
    comparison.
16. The lower dimension order is inherited from
    the public spherical-cap theorem at additive
    tolerance C=100, giving d>=L^2/116.
    This establishes Θ(L^2) along dyadic k.
17. Binary gluing removes the dyadic restriction. A
    one-dimensional independent Gaussian selector chooses
    block j with exact probability q_j/k. A shared
    data block implements each dyadic conditional partition,
    so the final mass is exactly (q_j/k)*(1/q_j)=1/k.
18. The data-coordinate squared centroid contribution
    is exactly sum_j (q_j/k)^2 P_j; the selector
    contribution is nonnegative and can be discarded.
19. Sorted binary powers have w_j=q_j/k<=2^(1-j),
    so entropy H(w)<=4 log2 by a geometric
    reference law and KL positivity. This bound is
    uniform even when k has many nonzero binary digits.
20. The all-mass squared hazard Lipschitz bound yields
    at most 2H(w) additional loss. Small powers below
    Q0=2^r0 have total size <Q0, and their omitted
    contribution is at most 2Q0 log(k)/k; this is <=1
    for k>=Q0^2. The dyadic proof already yields 88/q relative to the separate halfspace envelope; thus 88+8log2+1<95, for
    all sufficiently large integer k.
21. Combining the all-k upper construction with the
    independent spherical-cap converse at C=95 gives
    the optimal Theta(log^2 k) dimension order for all k.
    No finite-k Standard Simplex global optimizer is inferred.

## Replay requirements and limitations

The checker is Python 3 standard library only. It exhaustively
checks the combinatorial character-pair counts for r=2,...,7,
including all possible uniformly random generator columns,
and checks an explicit full-rank code orbit under sign flips.
It also certifies **exactly rational** numerical inequalities
used in the error budget and the logarithm threshold.
A separate check over 19 binary-expansion examples verifies
all-integer selector combinatorics, the geometric small-block
sum, and H(w)<4log2 with outward-rational logarithm intervals.
No floating point or optimizer is used.

These finite checks are *not* the proof of the conditional
Gaussian tilt or the Berry–Esseen theorem. Every universal
probabilistic inequality is written in paper.md with the
relevant assumptions, and the Berry–Esseen theorem has
a bibliographic locator in LITERATURE.md.

The result establishes the optimal *order* of dimension
complexity for all sufficiently large integers k, with
a fixed additive 95/k error tolerance. Exact leading
constants and finite-k optimizers remain outside its scope.
