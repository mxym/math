# The Gaussian deficit in the subquadratic spherical Khinchin inequality

**Yongxian Zhang · 19 November 2026**

For independent uniforms $\xi_j$ on $S^{d-1}$, let $G$ have the same covariance as a sphere point: $G\sim N(0,I_d/d)$. For every fixed $0<p<2$ there is $c_p>0$ such that every $d\ge3$ and every finite normalized real coefficient list $\sum_j a_j^2=1$ satisfy
$$
\mathbb E\left|\sum_j a_j\xi_j\right|^p-\mathbb E|G|^p
\ \ge\ \frac{c_p}{d}\sum_j a_j^4 .
$$
Thus the qualitative lower bound loses at least a quartic term away from its diffuse Gaussian limit. This is the higher-dimensional subquadratic conjecture in [Jakimiuk–Tang–Tkocz, §3](https://doi.org/10.1007/s00209-026-04016-5). For the best coefficient multiplying $\sum_j a_j^4$, its leading term as $d\to\infty$ is $p(2-p)/(4d)$.

1. [Radial proof when $d+p>4$](RADIAL.md). Adapt the authors' Gaussian replacement and spherical differentiation, with the opposite curvature and mollification across the origin.
2. [The missing range on the two-sphere](THREE.md). For $0<p<1$, use the Fourier and strengthened non-diffuse estimates of Chasapis–Gurushankar–Tkocz; for $p=1$ integrate the spherical mean exactly.
3. [Asymptotically best coefficient in high dimension](HIGH-D.md). The retained chi-square fluctuations and a single sphere summand give matching limits.

There is no claim about dimensions one or two, the finite-dimensional best coefficient, or the stronger comparison with a flat list of **fixed length**. No new qualitative Gaussian extremizer or new spherical differentiation principle is claimed.

[Primary sources and overlap check](SOURCES.md) · [internal review of the main theorem](REVIEW.md) · [internal review of the asymptote](HIGH-D-REVIEW.md). The proof is analytic. The optional standard-library command `python3 -B -O check.py` checks a finite set of normalization and calculus identities only ([output](CHECKS.txt)); the file digests are in [SHA256SUMS](SHA256SUMS). AI-assisted work with separate internal AI review; not externally peer-reviewed or formally verified. The searches do not establish priority.
