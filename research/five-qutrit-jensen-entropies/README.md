# Five qutrits and the negative type of quantum Jensen entropies

Can the square root of an entropy Jensen gap between mixed quantum states be represented as a distance in a real Hilbert space? A necessary condition is that the gap have **negative type**: every zero-sum weighted contrast of pairwise gaps must be nonpositive. Five states suffice to make that contrast positive.

| Entropy used in the gap | What the five states show |
|---|---|
| Tsallis, $0<q<2$ | **The same** five full-rank three-dimensional states and the same integer coefficients violate negative type for all orders. At $q=2$, the gap is one quarter of squared Hilbert–Schmidt distance, so it does have negative type. |
| Rényi, $0<q<1$ | **For each fixed order**, five full-rank three-dimensional states violate negative type. A small scale in this construction may depend on the order. No simultaneous Rényi witness is asserted. |
| Shannon, $q=1$ | The two families agree. A five-qutrit counterexample was already known from Zhang; it also persists for orders close to one by continuity. |

Sra's four-point theorem makes **five the smallest possible number of states** at every order of failure above. The square roots remain metrics: a failure of Hilbert-space embedding is not a failure of the triangle inequality. The comparisons concern the ordinary entropy of a midpoint minus the mean entropy of its endpoints, not a Tsallis centroid distance.

**中文摘要。** 同一组五个满秩三维量子态与整数权重，对所有 $0<q<2$ 同时否定 Jensen–Tsallis 散度的负型性。Jensen–Rényi 的结论是对每个固定 $0<q<1$ 都有五态反例，所用参数可随 $q$ 改变。四态总满足负型是 Sra 的已有定理；Shannon 五态反例及其临近阶数的延拓也不作为新结果。这不否定平方根距离的三角不等式。

[Full proof](PROOF.md) · [Independent internal review and numerical-check boundaries](REVIEW.md)

## What was known

* [Briët and Harremoës, 2009, §VI](https://doi.org/10.1103/PhysRevA.79.052311) described exponential convexity of the trace exponential as a possible route to negative type across entropy orders. Their exponential conjecture and its expected implication are distinct; the latter is not a separately numbered conjecture. The [trureturing trace-exponential counterexample](https://the-omega-institute.github.io/trureturing-mdbook/Blueprint/D5/S3/Divergence/TraceExpExponentialConvexityRefutation.html) concerns that route, not the five-state normalized entropy contrasts proved here.
* [Martins, Smith, Xing, Aguiar and Figueiredo, Proposition 38](https://jmlr.csail.mit.edu/papers/volume10/martins09a/martins09a.pdf#page=24) gives negative type of these unweighted divergences on **classical** distributions in the relevant ranges. This includes commuting quantum states. [Virosztek, Theorem 2](https://arxiv.org/pdf/1910.10447#page=3) gives the Carlen–Lieb–Seiringer qubit embedding result for operator-convex generators, including the Tsallis negative-entropy generators here. The logarithmic transfer used by Martins et al. and Sra also gives the corresponding qubit Rényi conclusion from the qubit Tsallis result. These are not new positive results of this note. [Sra, 2021](https://doi.org/10.1016/j.laa.2020.12.023) established metricity for the square roots in the relevant ranges.
* [Zhang, 2026, §§9.2–9.3, Example 9.6](https://arxiv.org/html/2602.08164v1#S9.SS3) gave five explicit full-rank qutrits violating Shannon negative type, using an unnormalized two-dimensional block and a scalar supplement to reach trace one. By continuity his same strict witness already applies to Tsallis and Rényi parameters in a neighborhood of one within their respective ranges. Its contrast at Tsallis order two is $-1/16$ with ordinary trace, so continuity of that witness does not extend it to the entire open interval.
* [Sra, October 2026, Proposition 2.5 and Theorem B.1](https://hexagonmath.org/pdf/2610.00602v1) proved both the four-point result for these entropy gaps and a five-point obstruction for a *different* log-determinant divergence on the positive cone. After a common affine transformation of the blocks, a reordering, and rescaling the contrast, **the five upper blocks and weights used here are his configuration**: two scalar matrices and three matrices from equiangular rank-one projectors. His earlier numerical five-point log-determinant example also predates this note. The calculation here combines that geometry with trace normalization, tracks the scalar supplement by an exact fourth-difference estimate, and separately treats the logarithm in the Rényi entropy.

This AI-assisted research draft was checked in a separate internal AI review. It has not been externally peer reviewed or formally verified. A targeted search of papers, announcements and prior repository results did not locate the precise all-order normalized statements; that search does not establish historical priority.

## Reproduce the checks

From this directory, with Python 3.10+ and no external packages:

~~~sh
python3 -BO verify.py
python3 -BO independent.py
~~~

Both scripts reconstruct all 25 midpoint spectra exactly. The second factors the characteristic polynomials directly and checks the order-two limit of Zhang's contrast. The finite decimal samples in the first are diagnostics only. The proof of the continuum of orders is the fourth-derivative inequality and, for Rényi, the fixed-order limiting argument.
