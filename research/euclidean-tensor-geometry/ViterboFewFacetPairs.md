# The EHZ volume inequality with few opposite facet pairs

**Yongxian Zhang.** AI-assisted proof development and internal verification; no claim of external peer review or priority.

Let \(K\) be a full-dimensional centrally symmetric polytope in standard \(\mathbb R^{2n}\), with \(n\ge2\) and \(m\) pairs of opposite facets. Then
\[
\frac{c_{\rm EHZ}(K)^n}{n!\operatorname{vol}_{2n}(K)}
\le \frac{1}{n!}\left(\frac{m(m-1)}{3n}\right)^{n/2}.
\]
The inequality \(c_{\rm EHZ}(K)^n<n!\operatorname{vol}_{2n}(K)\) follows whenever \([m(m-1)]^n<(3n)^n(n!)^2\). For example, this proves it for all centrally symmetric 12-dimensional polytopes with at most 13 facet pairs. The bound applies to the full EHZ capacity, not only affine symplectic embeddings. This extends the geometric scope of the [parallelotope theorem](https://github.com/mxym/math/releases/tag/viterbo-parallelotopes-v1.0.0), without modifying that version or implying the inequality for all centrally symmetric bodies.

## Normal matrix and central sections

Center \(K\) at zero and write \(K=\{x:|\langle v_i,x\rangle|\le1,\ 1\le i\le m\}\), with one normalized covector for each opposite pair. Write \(V\) for the \(m\times 2n\) matrix with rows \(v_i^{\mathsf T}\) and \(J\) for the standard symplectic matrix. The map \(x\mapsto Vx\) identifies \(K\) with \({\rm im}\,V\cap[-1,1]^m\), with section Jacobian \(\sqrt{\det(V^{\mathsf T}V)}\). [Vaaler, Theorem 1](https://msp.org/pjm/1979/83-2/pjm-v83-n2-p24-p.pdf), applied to the central section and rescaled to side length two, gives
\[
\operatorname{vol}_{2n}(K)\ge4^n/\sqrt{\det(V^{\mathsf T}V)}.
\]

Let \(S=VJV^{\mathsf T}\). In a thin QR factorization \(V=UR\) with \(U^{\mathsf T}U=I_{2n}\), the nonzero singular values of \(S\) are the singular values of \(RJR^{\mathsf T}\), namely \(\sigma_1,\sigma_1,\ldots,\sigma_n,\sigma_n\) for positive \(\sigma_i\). Then \(\prod_j\sigma_j=\sqrt{\det(R J R^{\mathsf T})}=|\det R|\), which is the section Jacobian, and \(\sum_j\sigma_j^2=\sum_{i<j}|S_{ij}|^2\). Applying the arithmetic–geometric mean inequality to the \(\sigma_j^2\) gives
\[
\sqrt{\det(V^{\mathsf T}V)}
\le\left(\frac{\sum_{i<j}|S_{ij}|^2}{n}\right)^{n/2}.
\]
Both arguments use the full rectangular normal matrix.

## Pairing tests and consequences

Write \(M=c_{\rm EHZ}(K)^{-1}\) and \(x_{ij}=|S_{ij}|/(4M)\). [Haim-Kislev's symmetric facet formula, Corollary 1.2](https://arxiv.org/html/1712.03494#S1), with facet weights summing to one after normalization, gives the [pair and triple inequalities](https://github.com/mxym/math/blob/viterbo-parallelotopes-v1.0.0/ViterboParallelotopes.md#1-pair-and-triple-tests): \(x_{ij}\le1\) and each triple of representatives has squared pairing sum at most two. These tests require only ordering, signing, and weighting the representative normals, not their independence. Summing over triples gives \(\sum_{i<j}x_{ij}^2\le m(m-1)/3\). Combining this with the section and Jacobian estimates proves the theorem; before using the triple sum, the sharper bound is
\[
\frac{c_{\rm EHZ}(K)^n}{n!\operatorname{vol}_{2n}(K)}
 \le\frac{(\sum_{i<j} x_{ij}^2/n)^{n/2}}{n!}.
\]
In particular, a condition purely on the covectors suffices:
\[
\frac{\sum_{i<j}|S_{ij}|^2}{\max_{i<j}|S_{ij}|^2}\le n(n!)^{2/n}.
\]
The denominator is positive because \(V\) has full column rank. The number of nonzero upper-triangular pairings can replace the left side as a sufficient condition. This criterion does not separately require a bound on \(m\).

For a refinement depending only on \(m\), color each edge of the \(m\) representatives according as \(x_{ij}\ge1/2\) or \(x_{ij}<1/2\). The stronger triple test from the same proof gives squared sum at most \(9/5\) on a monochromatic triangle. A nonmonochromatic triangle uses two mixed wedges; each vertex is the center of at most \(\lfloor(m-1)^2/4\rfloor\) mixed wedges. Thus the number of monochromatic triangles is at least
\[
L_m=\binom m3-\left\lfloor m\left\lfloor(m-1)^2/4\right\rfloor/2\right\rfloor.
\]
Since each edge belongs to \(m-2\) triples, we can replace \(m(m-1)/3\) by \(B_m=m(m-1)/3-L_m/[5(m-2)]\) inside the main power. For \(n=6,7,8,10,20,30\), this certifies a strict inequality through \(m=13,16,19,25,65,116\), respectively. The comparisons just raise the bound to its square and compare integers. For example, in dimensions 14 and 16 the refined test covers 32 and 38 total facets, respectively.

The basic leading coefficient is \(1/3\) in its bound on \(\sum x_{ij}^2\); the mixed-wedge counting lowers it to \(13/40\). By Stirling, it follows that \(m\le \eta n^{3/2}\) suffices at all sufficiently large \(n\) for any fixed \(\eta<\sqrt{40/13}/e\). The simpler sufficient bound \(m\le(3/5)n^{3/2}\) holds whenever feasible, by \(n!>(n/e)^n\) and \(3/5<\sqrt 3/e\).

The geometric inputs above are classical. The new step here is the use of the alternating skew spectrum to express the section Jacobian and bound it from the same pairings tested by the facet formula. A bounded literature check did not find an equivalent facet-count criterion. The [unrestricted EHZ volume inequality is false](https://annals.math.princeton.edu/2026/203-2/p05); no unrestricted centrally symmetric statement is made here.
