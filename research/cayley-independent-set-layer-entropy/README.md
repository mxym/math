# Independent-set counts on uniform labeled trees: sharp loss and layer entropy

Research note by Yongxian Zhang. The proofs were independently replayed as documented in REVIEW.md; that check is not external peer review.

Let $T_n$ be a uniformly random labeled tree, $i_k(T_n)$ its number of independent $k$-sets, and $a=k/n$.

* **Sparse scale (MOBILE.md):** For every $n^{5/6}\ll k=o(n)$, the logarithm of the ratio to the exact expected count, divided by $k^6/n^5$, tends in probability to $-1/4$. No extra logarithmic separation is required.
* **Fixed densities (ENTROPY.md):** For $k/n\to a$ strictly between 0 and the limiting independence ratio, the normalized log count has a deterministic typical limit given by a canonical-pressure Legendre transform. It is strictly below the entropy of the expected count, by $a^6/4+O(a^7)$ as the fixed density tends to zero. This is not a claim about the expectation of the log count, or about the independence endpoint. The elementary leaf test separately yields a one-sided, nonsharp rate through $k=n-1$.

The preceding repository results described the sparse concentration/lognormal/collapse transition and the improvement over the path. These are different conclusions; see SOURCES.md for the precise comparison and prior methods. No worldwide priority is asserted.

Reproduce the exact arithmetic from this directory with Python 3:

```sh
sha256sum -c SHA256SUMS
python -O series.py
python -O coefficient_check.py
python -O independent.py
```
