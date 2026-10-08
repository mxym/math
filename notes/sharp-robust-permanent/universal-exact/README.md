# Universal exact finite \((n,k)\) atom-TV coefficient: determinant formula

**Main result:** [Complete theorem, explicit integer formula and proof](paper.md).

For the natural \(S_n\)-action on \(k\)-subsets, this note gives a **finite maximum of explicit integer maximal-minor ratios** equal to the sharp marginal-preserving single-atom total-variation constant \(C_{n,k}\), for **every finite** \(n\ge1,\ 0\le k\le n\). It **does not require an LP solver** and gives a genuine nonnegative attaining perturbation.

Set \(m=\min(k,n-k)\), enumerate feasible short-cycle vectors \(c=(c_1,\ldots,c_m)\) with remainder \(n-\sum jc_j\) equal to zero or at least \(m+1\), and calculate the orbital count columns \(a_c=(1,F_0(c),\ldots,F_{m-1}(c))^T\) by the already proved integer transfer-matrix recurrence.

For each selection of \(m+1\) other vectors together with the identity column, let \(\Delta_i\) be the alternating maximal minors of the resulting \((m+1)\times(m+2)\) integer matrix. The **exact value** is

\[
\boxed{C_{n,k}=
\max\frac{2|\Delta_0|}{\sum_i|\Delta_i|}},
\]

omitting zero denominators (with the exceptional \(m=0\) cases treated separately). All maxima are over an **explicit finite set depending only on \((n,k)\)**.

## Mathematical advances over the previous orbital LP

The theorem eliminates continuous LP variables and solver assumptions. Its proof establishes:

- **Exact full-rank certificate** \(\det A_{\mathrm{special}}=(-1)^m\prod_{r=0}^{m-1}\binom{n-2r}{m-r}\ne0\), for every \(n\ge2m\).
- **Circuit extremality:** an optimal signed marginal-preserving perturbation exists on at most \(m+2\) short-cycle profiles/conjugacy classes.
- **Exact rational attainment:** alternating maximal minors give both the optimal constant and explicit positive/negative central class mixtures with exactly matching marginals.
- **Terminating algorithm:** a bounded finite maximum of integer determinants and rational comparisons. For every fixed \(m\), the number of candidate matrices is polynomial in \(n\), albeit with a potentially high exponent.
- **Explicit rational-height bound:** reduced denominator at most \((m+2)(m+1)!\binom nm^m\).

**Interpretation:** this closes the arbitrary finite-parameter *exact evaluability* problem in a determinant-minor sense. It does **not** establish an elementary piecewise-rational expression with a bounded number of branches independent of \(n,k\). A structural classification of the maximizing short-cycle supports at all parameter pairs remains an additional, stronger problem.

## Reproduce the exact integer implementation

From the root of the public repository, using only Python 3.9+ standard library:

```bash
python notes/sharp-robust-permanent/code/check_universal_max_minors.py
python notes/sharp-robust-permanent/code/check_universal_max_minors.py 9 4
```

The checker imports the independently developed and published exact cycle transfer recurrence at
[code/check_all_k_orbital_compression.py](../code/check_all_k_orbital_compression.py).
Its integer Bareiss determinant routine checks the cofactor kernel identity for every nonzero candidate, performs the **entire** finite maximization (never early-stops and calls no optimizer), and replays historical exact values in ranks 1–4 including \((n,k)=(9,4)\), which requires 118,755 candidate matrices. It also verifies the binomial-product rank determinant for ranks 1–9 and multiple degrees.

### Proof scope and release

The full mathematical proof is in [paper.md](paper.md), independent of the finite examples. The previous [complete proof dossier](../paper.md), [standalone 21-page fixed-rank asymptotic paper](../focused-paper/v2/paper.pdf), and [verification record](../VERIFICATION.md) remain preserved.

This is an AI-assisted research proof draft. The integer checker is not a Lean kernel proof; independent mathematical refereeing, full Lean formalization, and systematic literature novelty review are still pending. In particular, a simple non-maximization casewise rational formula has **not** been established.
