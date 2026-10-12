# Projection-volume results: spectral finiteness, dimensionwise stability, and historical hashes

**Dated clarification, 7 October 2026.** This note concerns entry 005 as inspected at commit `9af06fa4cadaa80e176ed633a7176ed7f2e813db`. It corrects an overbroad phrase in the v3 research log, makes the v2 spectral supplement's finiteness justification explicit, and records a navigation-only historical hash difference. **No theorem statement or proof is changed.** Frozen version files and their recorded manifests are left untouched.

## 1. The unrestricted spectral supremum is finite for a specific exponential reason

For a full-dimensional convex body $K\subset\mathbb R^n$, use exactly the normalization of entry 005:

$$R_n(K)=\frac{|\Pi K|}{|K|^{n-1}},\qquad
h_{\Pi K}(u)=|\operatorname{proj}_{u^\perp}K|_{n-1}
\quad(\|u\|=1).$$

The v2 spectral supplement proves, for a join-closed family containing a point,

$$\lim_{n\to\infty}\sup_{K\in\mathcal F_n}R_n(K)^{1/n}
=e\sup_{K\in\mathcal F}\lambda(K),\qquad
\lambda(K)=\left(\frac{a(K)R(K)}{g(\dim K)}\right)^{1/(\dim K+1)}.$$

The sentence attributing finiteness to “classical dimension-dependent upper bounds” should be read with the following explicit rate bound. **Finiteness in each fixed dimension alone would not suffice.**

Lutwak–Yang–Zhang, Corollary 4.12, prove for all convex bodies that

$$R_n(K)\le B_n:=\frac{n^n(n+1)^{(n+1)/2}}{(n!)^{3/2}}.$$

Their projection-body definition has the same support-function normalization displayed above. The corollary explicitly extends from polytopes to all convex bodies. See their [definition, PDF page 1](https://cims.nyu.edu/~yangd/papers/trans.pdf#page=1) and [Corollary 4.12, PDF page 11](https://cims.nyu.edu/~yangd/papers/trans.pdf#page=11).

Stirling's formula gives $B_n^{1/n}\to e^{3/2}$. The padded self-joins of any fixed body have limiting root $e\lambda(K)$, so this estimate gives

$$1\le\lambda_{\rm all}\le\sqrt e<\infty,\qquad
\lim_{n\to\infty}M_n^{1/n}=e\lambda_{\rm all}\le e^{3/2},$$

where $M_n=\sup_K R_n(K)$. This supplies the omitted growth justification. It does not determine the exact supremum or claim a new best-known upper bound.

The existing self-similar family's spectral values tend to $\Lambda/e$. Accordingly, the sufficient condition for a finite body to improve its limiting exponential rate is specifically $\lambda(K)>\Lambda/e$. Exceeding only a finite sampled spectral value would not establish that improvement.

## 2. Stability is uniform in each fixed dimension, not across dimensions

Theorem 5.1 of v3 correctly fixes $d$ and asserts a modulus $\delta(d,\varepsilon)>0$, uniform over all bodies of that dimension and all their maximum-volume inscribed simplices. Its proof is correct. The phrase “dimension-uniform qualitative stability statement” in the v3 research log should instead read:

> a qualitative stability statement uniform over convex bodies in each fixed dimension

There is no dimension-independent modulus in the stated additive defect. The following explicit family makes the distinction necessary.

Let $K_m=T_m\times T_m$, of dimension $2m$, where $T_m=\operatorname{conv}(0,e_1,\ldots,e_m)$. The product rule gives

$$a(K_m)=\frac1{m+1},\qquad
a(K_m)-\frac1{2m+1}
=\frac{m}{(m+1)(2m+1)}\longrightarrow0.$$

Every maximum-volume inscribed simplex $S_m$ in $K_m$ has volume $1/(2m)!$, whereas $|K_m|=1/(m!)^2$. Thus

$$\frac{|K_m|}{|S_m|}=\binom{2m}{m}.$$

Here is an elementary verification of the largest-simplex volume. A maximum inscribed simplex can be chosen with all vertices among the vertices of $K_m$: absolute determinant is convex in each vertex separately, so replacing the vertices one at a time by extreme points does not decrease the maximum. Label a product vertex by a pair $(i,j)$, $0\le i,j\le m$. For any $2m+1$ such vertices, their augmented affine-coordinate determinant agrees up to sign with a maximal minor of the signed vertex-edge incidence matrix of the bipartite graph on these two sets of $m+1$ labels. One row is deleted, and elementary determinant-preserving row operations recover the affine-coordinate matrix. The minor is zero if the chosen edges contain a cycle; otherwise they form a spanning tree and repeated leaf elimination makes its absolute determinant one. Hence every vertex simplex has volume zero or $1/(2m)!$. The simplex with vertices $0,(e_i,0),(0,e_j)$ attains the latter value.

If $K_m$ were contained in $z+(1+\varepsilon)(S_m-z)$, volume comparison would force

$$\binom{2m}{m}\le(1+\varepsilon)^{2m}.$$

But $\binom{2m}{m}^{1/(2m)}\to2$, so this fails for all sufficiently large $m$ for every fixed $0<\varepsilon<1$, including $\varepsilon=1/2$. The invariant defect nevertheless tends to zero. This disproves the dimension-independent reading of the research-log phrase, without affecting the actual fixed-dimension theorem.

## 3. Historical v2 manifest and the later navigation link

The v2 manifest matches all fifteen of its listed files at the audited historical commit `8bacac8e50b668782229b3c200fd44e959d618d1`. It records the original v2 README as:

- 4,945 bytes
- SHA-256 `46dc291a8315652f04eee340342e745141fbc37f30e18f9f6affb3023a61ac11`

A later navigation-only commit, [`c3a3de548bda57835deefcd5e670cb5ff61dcce6`](https://github.com/mxym/math/commit/c3a3de548bda57835deefcd5e670cb5ff61dcce6), added a link to the spectral supplement in that README's opening paragraph. At the inspected head, its values are:

- 5,012 bytes
- SHA-256 `01137c32bc9d76ed786995c08cb10abf1669295943b36ac972e1ee251ed8f6f8`

This README is the **sole mismatch** when the historical v2 manifest is checked against the later head. The v2 paper, producer, checker, certificate, proof audit and all other manifest-listed files retain their recorded hashes. The spectral supplement was added after the original manifest and is not listed in it; v3 separately pins that supplement as a proof dependency.

The original manifest remains a historical snapshot and is not silently regenerated. To reproduce it, check the pinned historical commit rather than the evolving navigation file. The v3 manifest's fifteen version-file hashes and two inherited-input hashes all match at the inspected head.

## 4. Verification and unchanged scope

A separate exact audit reproduced the v3 producer byte-for-byte and obtained the published checker report in ordinary and optimized Python modes. Additional checks covered 256 centered rational laws and 90 spectral-amplification cases; the largest-simplex determinant calculation above was exhaustively checked for $m=1,2,3$. The infinite statements rest on written proofs, not these finite tests.

The general-body simplex equality theorem, fixed-dimension qualitative stability theorem, symmetric boundary-law bound and explicit spectral nonattainment theorem are unchanged. The optimal asymptotic constant, an effective stability modulus, and the complete higher-dimensional symmetric equality class remain open within this record. This clarification makes no priority or external peer-review claim.
