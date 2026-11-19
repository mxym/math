# Inversion-weighted growth for finitely based permutation classes

Fix $0<q<1$ and let $Z_n(q)=\sum_{\sigma\in\mathrm{Av}_n(B)}q^{\mathrm{inv}(\sigma)}$ for a finite classical basis $B$. The shape of a few forbidden patterns distinguishes three possible orders.

| Basis | Result |
| --- | --- |
| No forbidden pattern is a direct sum of singletons and descents $21$ | The fixed-$q$ exponential growth rate exists and is at least $(1+\sqrt{1+4q})/2$. There is no formula here for every exponential rate. |
| Such a forbidden pattern exists, but no increasing identity is forbidden | If $r$ is the smallest number of descents $21$ in any such forbidden pattern, $Z_n(q)$ equals a polynomial in $n$ of exact degree $r-1$, **up to an exponentially small error**. Its coefficients are holomorphic on $|q|<1$; on $|q|\le t<u<1$ the error is $O_{B,t,u}(u^n)$. |
| An increasing identity is forbidden | If a decreasing pattern is also forbidden, the class is finite. Otherwise let $d+1$ be the fewest decreasing layers in any layered forbidden pattern. Then $n^{-2}\log Z_n(q)\to\log(q)/(2d)$ and the tilted plot concentrates at the balanced $d$-layer decreasing permuton, with exponentially small (speed $n^2$) probability outside any fixed weak neighborhood. |

The classical core/padding and Fibonacci-pattern dichotomy at **fixed inversion count** are due to Claesson–Jelínek–Steingrímsson. Here a core estimate uniform over inversion counts permits summing on the whole unit disk. For polynomial-regime classes, the number with $k$ inversions is at most $(1+n)^{r-1}\exp(C_B\sqrt{k+1})$. For **1324**, combining this estimate with the exact low-inversion counts of Linusson–Verkama gives a first finite-size correction and, for all sufficiently large $n$, strict monotonicity of the weighted totals $Z_{n+1}(q)>Z_n(q)$ simultaneously for $0<q\le e^{-D/\sqrt n}$ for some absolute $D$. This is not a proof of coefficientwise inversion monotonicity, the conjectured sharp two-partition bound, or a new Stanley–Wilf estimate. The identity-forbidden shape argument uses the classical Erdős–Stone and Erdős–Simonovits results.

- [Polynomial and exponential regimes; fixed-$q$ 1324 correction](DICHOTOMY.md) and [review](DICHOTOMY-REVIEW.md).
- [Square-root envelope and uniform weighted window](ENVELOPE.md) and [review](ENVELOPE-REVIEW.md).
- [Quadratic rate and unique shape](QUADRATIC.md) and [review](QUADRATIC-REVIEW.md).
- [Sources and priority boundaries](SOURCES.md); [finite verification](check_growth.py) and [expected output](CHECKS.txt). Run `python3 -BO check_growth.py` then `sha256sum -c SHA256SUMS`.

All three proofs received separate internal AI review, not external peer review. No priority guarantee.
