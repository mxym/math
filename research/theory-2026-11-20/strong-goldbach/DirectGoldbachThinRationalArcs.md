# Thin rational arcs in the actual fixed-target binary Goldbach coefficient

This is an elementary direct application of the additive large sieve to the true prime–prime convolution. No parity proxy, new arithmetic-distribution theorem, or Goldbach lower bound is asserted.

Let \(L=\log N\). Suppose \(F(\alpha)=\sum_{1\le n\le N}f_ne(n\alpha)\), \(G(\alpha)=\sum_{1\le n\le N}g_ne(n\alpha)\), where \(\|f\|_2\|g\|_2\ll N L^C\). For arbitrary bounded weights on true primes and a factor \(\log p\) in each sum, one may take \(C=1\), by the prime number theorem. In particular this includes the exact weighted true prime polynomial of the [reflection-even central test](CentralEvenPrimitiveGoldbachCriterion.md); cutting to \((p,N)=1\) does not raise its norm.

For \(1\le R\le N\) and a width \(\Delta>0\), let \(\mathcal A(R,\Delta)\) be the union on the circle of intervals of radius \(\Delta\) at all reduced fractions \(a/q\) with \(R<q\le2R\). The [additive large sieve](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf) gives
\[
 \int_{\mathcal A(R,\Delta)} |F(\alpha)G(\alpha)|\,d\alpha
 \ll \Delta (N+R^2)\|f\|_2\|g\|_2 .
\]
Indeed for fixed \(\theta\) the shifted coefficients \(f_ne(n\theta),g_ne(n\theta)\) retain their squared norms. The rational samples have spacing \(\gg R^{-2}\). Apply the large sieve to each polynomial and Cauchy–Schwarz to their pairwise sampled product, then integrate \(|\theta|\le\Delta\). Overlap simply overcounts a nonnegative integral.

Thus on actual arcs
\[
 |\alpha-a/q|\le L^B/(qN),\qquad L^D\le q\le N/L^D,\quad (a,q)=1 ,
\]
the \(e(-N\alpha)\)-weighted contribution to the true convolution is \(O_A(NL^{-A})\), uniformly in the fixed \(N\) and in the described weights, for any specified \(A,B\), taking \(D>A+B+C+3\). In fact each dyadic shell is bounded by \(O(L^{B+C}(N/R+R))\); summing these two geometric tails costs only a constant times \(N/L^D\), and proves the stated estimate (the slightly larger stated \(D\) is convenient). There is no positivity assumption in this deletion, as the contribution is bounded in absolute integral. If the usual low-denominator major arcs are treated separately, delete only the part of these narrow intervals outside those major arcs; the same estimate applies irrespective of overlap.

This does **not** cover the full minor arcs. The union here has measure \(O(L^{B-D})\). With \(q\le N/L^D\), Dirichlet approximation only supplies the wider scale \(L^D/(qN)\) for coverage, and plugging this larger width into the estimate loses the logarithmic saving. A genuinely signed fixed-target bound on the frequencies still uncovered is needed to turn the central positive major-arc main term into a lower bound for an actual prime pair.
