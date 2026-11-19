# Eventual inclusion monotonicity for the volume of a random polytope

Let \(V_n(K)\) be the expected volume of the convex hull of \(n\) independent uniform points in a convex body \(K\). Enlarging \(K\) **can** decrease this expectation at a fixed small sample size. Rademacher asked whether there is nevertheless a sample threshold depending only on dimension, not on the two nested bodies (2012, Discussion, question 1, after Meckes and Reitzner). Beermann and Reitzner repeated the question in 2017.

**Theorem.** For every dimension \(d\) there are computable constants \(N_d\) and \(a_d>0\) such that, for every \(n\ge N_d\) and every pair of full-dimensional convex bodies \(K\subset L\) in \(\mathbb R^d\),
\[
             V_n(L)-V_n(K)\ \ge\ a_d\bigl(|L|-|K|\bigr).
\]
In particular the increase is strict for proper inclusion. The comparison is for actual volumes, not volume fractions of their respective bodies. The threshold and coefficient are very conservative; neither is claimed optimal.

**Why it becomes true.** Starting from \(m\) uniform points in \(K\), adding a *specified exterior point* gains at least a dimension-dependent constant times \(|K|/m\): with positive probability a small cap near the point has the right \(d\) samples to form a new simplex. An *ordinary extra uniform point* gains \(o_d(|K|/m)\) uniformly in \(K\). To see why, hold out half the points; a given location can be lost upon deleting at most \(d+1\) labels and cannot be lost at all if the first-half hull already covered it. Tiny enlargements of \(K\) can then be chained to compare arbitrary inclusions.

- [Complete analytic proof, with constants](PROOF.md)
- [Sources and overlap comparison](SOURCES.md)
- [Independent internal mathematical review of the frozen proof](REVIEW.md)
- [Optional standard-library exact consistency checks](check.py) and [their output](CHECKS.txt)

Run \(\texttt{python3 -B -O check.py}\) and \(\texttt{sha256sum -c SHA256SUMS}\) in this directory. The computation is illustrative and the proof is not contingent on the checks. No conclusion is claimed here about all small sample sizes, volume moments other than the first, or the number of faces. AI-assisted research with internal verification, not externally peer-reviewed; no priority guarantee.
