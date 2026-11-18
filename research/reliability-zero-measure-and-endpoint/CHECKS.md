# Verification and limits

The proofs are analytic. The following scripts are independent exact-arithmetic diagnostics, not evidence that finitely many orders suffice for an asymptotic result. Both use only the Python standard library and explicitly raise on failure, also when Python assertions are disabled.

From this directory run:

```sh
python3 -B -O verify.py
python3 -B -O independent.py
```

| Check | Route and outcome |
|---|---|
| Tree expansion and coefficient bounds | All 771 connected labelled simple graphs on 2–5 vertices. The first script compares 8,135 greedy-tree fibers with direct operational-edge subsets. The independent script reconstructs coefficients by partition-lattice Möbius inversion, divides by $(1-q)^{n-1}$, and obtains the tree count from a Laplacian minor. |
| Values at $q=-1$ | A component recurrence and logarithmic-derivative recurrence agree through $n=80$. Independently, grouping partitions by block size and using Entringer's triangle gives the exact signed endpoint through $n=33$. |
| Real-root brackets | Both methods give strictly opposite endpoint signs for eight matched intervals at $n=7,8,15,16,31,32,63,64$. No uniqueness claim is based on bisection. |

For example, at $n=64$ the checked interval is $(-899/1000,-898/1000)$. Under this normalization the root at 1 and every root multiplicity count in Theorem A.

**Review status.** The analytic claims were drafted with AI assistance and then checked in a separate AI-assisted review in the same workflow. The review re-derived both directions of the measure criterion and the asymptotic sandwich for the negative roots. It checked activity ordering, leading coefficient and atom at 1; the largest-block weight bound; the triangular array domination; uniformity in the parameter of Rouché's theorem and of the Cauchy remainder; and the distinction between the endpoint sign, qualitative convergence, and the first-order quantitative conclusion. No outside referee or proof assistant has certified these claims.

**For further review:** check the sharp factor 2 on both sides of the moving window, counting conventions in comparisons across variables, and priority under the Tutte / Mallows–Riordan names. Beyond the proven statements, exact finite root counts and extremality among all simple graphs are not addressed. The typical number of real roots of a random graph is not addressed; weak convergence does not rule out individual outliers.
