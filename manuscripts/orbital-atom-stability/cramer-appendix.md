## Appendix P. Exact rational-polynomial certificate for the infinite primal families

The primal families in Section 22.2 can be verified without a computer algebra
system. Let \(A_r(m)\) be the displayed five-by-five matrix, with columns
\(I,K,H,-T,-E\) in its moment rows and the two probability rows as in (118).
Let \(D_r=\det A_r\), and let \(N_I,N_K,N_H,N_T,N_E\) be its five Cramer
numerators, replacing the respective column by \((1,1,0,0,0)^T\).
All are polynomials over \(\mathbb Q\). The exact identities are
\[
A_r(m)(N_I,N_K,N_H,N_T,N_E)^T
 =D_r(m)(1,1,0,0,0)^T,
\]
\[
N_I+N_K+N_H=D_r,
\qquad N_T+N_E=D_r.
\]
For every residue \(r=0,1,2,3\), \(D_r,N_I,N_T\) have degree nine with
leading coefficient \(-192\). Their next coefficients are:

| Residue \(r\) | \([m^8]D_r\) | \([m^8]N_I\) | \([m^8]N_T\) |
| ---: | ---: | ---: | ---: |
| 0 | -304 | 560 | -48 |
| 1 | -752 | 112 | -496 |
| 2 | -1200 | -336 | -944 |
| 3 | -1616 | -752 | -1360 |

The other three numerators have degree eight with leading coefficients
\[
[m^8]N_K=-768,\qquad [m^8]N_H=-96,\qquad [m^8]N_E=-256.
\]
In all four cases \([m^8](D_r-N_I)=-864\) and
\([m^8](D_r-N_T)=-256\). Dividing the numerator polynomials by \(D_r\)
therefore gives exactly the five expansions in (120). Positive leading ratios
give eventual positivity; the degree-nine nonzero denominator gives eventual
invertibility. With four fixed residue classes these conclusions are uniform.
The concrete support types are distinct and realizable for \(m\ge6\);
the certificate also checks their short-cycle counts and remaining long cycle.

The independent
[rational-polynomial checker](../../verification/finalization/check_cramer_polynomials.py)
stores a polynomial as its finite list of Fraction coefficients. It constructs
the moment matrix directly from (99)--(100), expands each determinant by all
120 terms in the Leibniz formula, and compares every coefficient in the five
Cramer identities and both normalization identities. It checks the displayed
degree and leading/next coefficients, and supplies every full polynomial in
its [recorded output](../../verification/finalization/results/cramer-polynomials.json).
Thus it verifies identities for all parameter values, rather than testing
several integers \(m\). The analytic passage to eventual positivity and the
global dual inequalities are still the written steps of Theorem 22.

```sh
python3 -B verification/finalization/check_cramer_polynomials.py
python3 -O -B verification/finalization/check_cramer_polynomials.py
```

Both executions must produce the same exact coefficient lists. This independent
checker uses only standard-library integer and rational arithmetic, with explicit
guards that cannot be stripped by `-O`. It complements the earlier SymPy
expansion replay and does not require or trust a discovery optimizer.
