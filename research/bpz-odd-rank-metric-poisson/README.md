# Extremal rank-metric intersecting codes in large odd extension degrees

For every fixed prime power \(q\), Borello–Polverino–Zullo's extremal length \(2m-3\) is attained by a nondegenerate \([2m-3,3,m-1]_{q^m/q}\) rank-metric intersecting code for all sufficiently large odd \(m\). This gives an affirmative answer in the whole large-degree range of their Remark 4.4 and concluding question. It **does not** settle all smaller odd degrees for all fields.

The proof gives a density, not merely a first-moment bound: for a uniform \(3\)-by-\((m+3)\) matrix over \(\mathbb F_{q^m}\), the number of projective kernel lines of rank weight at most two tends in distribution to \(\mathrm{Poisson}(\mu_q)\), where
\[
\mu_q=\frac{q^6}{(q^2-1)(q^2-q)}.
\]
Thus the probability of obtaining the required scattered subspace tends to \(e^{-\mu_q}>0\). An explicit, deliberately coarse sufficient threshold is \(m\geq100(24q^2+2)^2\). The underlying critical-window Poisson theorem applies to any fixed rank cutoff \(t\geq2\) and number of check rows \(k\geq t\). Separate, exactly checked examples for \(q=2\) cover \(m=7,9,11\).

[PROOF.md](PROOF.md) contains the general probability theorem, its application, and the effective bound. [SOURCES.md](SOURCES.md) locates the original question and distinguishes earlier limits. Run `sh replay.sh | diff -u RESULTS.txt -` with Python 3 (assertions enabled) and a C++17 compiler. The programs independently verify the finite examples via enumeration of projective points and via scalar-intersection ranks. The asymptotic and threshold statements are proved analytically, not inferred from the examples.
