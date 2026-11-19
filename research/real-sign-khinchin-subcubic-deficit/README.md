# A quartic Gaussian deficit for real-sign sums when 2 < p < 3

**Yongxian Zhang · 19 November 2026**

Let the $\varepsilon_i$ be independent fair signs and $Z$ be standard real Gaussian. For each fixed $2<p<3$, there is a $b_p>0$ so that every real unit coefficient vector, of any finite length, satisfies
$$
 \mathbb E |Z|^p-\mathbb E\left|\sum_i a_i\varepsilon_i\right|^p\ \ge\ b_p\sum_i a_i^4 .
$$
This answers the **real-sign Gaussian-comparison** question in [Jakimiuk–Tang–Tkocz, §3](https://doi.org/10.1007/s00209-026-04016-5) in the missing open interval. Jakimiuk had proved the Gaussian stability statement for $p\ge3$. The separate fixed-length question, in which the comparison is with an equal-coefficient sign sum rather than a Gaussian, is **not** answered. The proof does not give the best $b_p$ or a positive deficit at $p=2$ (where the two moments coincide).

The [analytic proof](PROOF.md) starts from Haagerup's Fourier bound and Mordhorst's published sign-change theorem. Strictness of that integral on compact intervals, the low-frequency quartic term for diffuse coefficients, and the explicit fourth-moment interpolation bound for dominant coefficients give the uniform quantitative conclusion. The qualitative sharp Gaussian bound and the distribution-function machinery are prior, not introduced here.

[Primary literature, version and repository comparisons](SOURCES.md) · [independent internal review](REVIEW.md). The optional command `python3 -B -O check.py` checks finite algebraic identities ([output](CHECKS.txt), [hashes](SHA256SUMS)); it is not the proof. AI-assisted work, internally reviewed, not external peer review or formal verification. Priority is not guaranteed.
