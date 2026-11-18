# Taylor coefficients of an exponential product for two-spectrum Hermitian pairs

Let $H=A+B$ and let $Q_k$ be the $k$th derivative at zero of $e^{tA}e^{tB}$. If each of the Hermitian matrices $A,B$ has at most two distinct eigenvalues, then for every positive integer $k$,
$$
s(H^k)\prec_w s(\operatorname{Re}Q_k)\prec_w s(Q_k).
$$
Here $s$ lists singular values in decreasing order and $\prec_w$ compares their successive partial sums. The conclusion applies to every Hermitian pair of size two. It also applies to direct sums of such pairs, even when the whole matrices have more than two eigenvalues.

The key step is to control **both** two-dimensional partial sums: the largest singular value and the trace norm. The latter need not be the absolute trace when the power is odd. A separate, *signed* comparison substitutes eigenvalues for singular values on the first leg. Within the two-spectrum class, it holds at even orders. For each odd $k\ge5$, it holds exactly when the inputs commute or the sum of their spectral midpoints is nonnegative.

**What was known.** Orders one and two are elementary; Zhang proved orders three and four in all dimensions. The journal article already gives a two-dimensional failure of the signed comparison at order five, and prior Pauli examples give signed failure at every odd order from five. Forrester and Thompson explicitly gave the two-dimensional centered scalar trace-coefficient estimate. Its scalar shifts supply the signed trace obstruction. The argument here uses that earlier estimate to prove the two Ky Fan inequalities at all orders and applies the classical two-projections decomposition. It does **not** settle Zhang's higher-order problem for unrestricted matrices.

[Proof](PROOF.md) · [Sources and prior results](SOURCES.md) · [Internal review](REVIEW.md)

This is an AI-assisted research note, independently checked within the same AI research effort. It has not undergone external peer review. No assertion of worldwide priority is made.

## Reproduce the finite checks

Run in this directory with Python 3 (standard library only):
```sh
python3 verify.py
python3 independent.py
sha256sum -c SHA256SUMS
```
The first script expands real-matrix coefficients directly. The independent script uses Gaussian-integer matrices, a different recurrence, and exact comparisons of quadratic surds on both legs. [Recorded outputs](CHECKS.txt) are consistency checks, not a substitute for the all-orders proof.
