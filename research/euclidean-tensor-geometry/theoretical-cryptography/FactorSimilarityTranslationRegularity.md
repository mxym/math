# Translation regularity and geometric affine avoidance

Let \(0<q<1\), \(G_q=\{q^n:n\ge1\}\), and let \(E\subset\mathbb R\) be measurable. For finite-measure \(E\) put
\[
              D_E(h)=\|\mathbf 1_E(\cdot+h)-\mathbf 1_E\|_{L^1}.
\]
We give a necessary local roughness condition for signed affine avoidance of \(G_q\), an abundance estimate in the opposite direction, and one quantitative regularity bound that can still be achieved by avoiding compact sets.

**Theorem.**
1. If \(E\) avoids every \(x+sG_q\) with \(s\ne0\), then for every \(x\in\mathbb R\), each \(\sigma\in\{-1,1\}\), and every \(b>0\),
   \[
       \int_0^b\mathbf 1_{E^c}(x+\sigma h)\frac{dh}{h}=\infty.       \tag{1}
   \]
   If \(E\) has finite positive measure, then \(\int_0^b D_E(h)\,dh/h=\infty\).
2. For every \(\eta\in(0,1)\) there is a compact \(E\subset[0,1]\) with \(|E|>1-\eta\) avoiding all signed copies of \(G_q\) and satisfying
   \[
           D_E(h)=O_q\!\left(\frac1{\log\log\log(1/|h|)}\right)
                  \qquad(h\to0).                               \tag{2}
   \]
   The range of sufficiently small \(h\) may depend on \(\eta\). This upper bound is not an integrable Dini modulus and does not make the two directions a sharp threshold.

The affine avoidance itself for every fixed \(q\) is due to [OpenAI Mathematics](https://github.com/openai/math/tree/main/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026), and is explained in detail by [Iosevich–Yavicoli](https://arxiv.org/html/2611.02454v1). The new construction estimate below retains explicit complexity at the finite hitting and open-repair stages of that argument. It is not a new avoidance theorem for supergeometric patterns.

## 1. Directional Dini obstruction and abundance

Fix \(x,\sigma,b\). Consider the possible absolute dilations \(s\in[b,b/q]\). At index \(n\) the subset of bad dilations has measure
\[
 q^{-n}\int_{bq^n}^{bq^{n-1}}\mathbf 1_{E^c}(x+\sigma h)\,dh.
\]
On the displayed annulus \(b/h\le q^{-n}\le b/(qh)\); the annuli partition \((0,b]\) up to endpoints. If the integral in (1) were finite, the sum of bad-dilation measures would be finite. By the first Borel–Cantelli lemma almost every \(s\) would have only finitely many bad indices. The entire tail of such a progression is itself a copy \(x+(\sigma s q^j)G_q\), a contradiction. This argument is pointwise at each \(x\), not only at almost every center. Integration over \(x\in E\), using translation invariance and \(|E\setminus(E-h)|=D_E(h)/2\), gives the global divergence for positive finite measure.

There is also a useful direct estimate without a tail deletion. If \(0<|E|<\infty\), let
\[
 {\cal C}_b^\sigma(E)=\{(x,s):x\in E,\ b\le s\le b/q,\
                    x+\sigma s q^n\in E\ \text{for every }n\ge1\}.
\]
The union bound and the same annuli give
\[
 1-\frac{|{\cal C}_b^\sigma(E)|}{|E|\,(b/q-b)}
      \ \le\ \frac{1}{2(1-q)|E|}\int_0^b\frac{D_E(h)}h\,dh.         \tag{3}
\]
Thus finite logarithmic perimeter in the sense \(\int_0^1 D_E(h)\,dh/h<\infty\) forces asymptotically full measure of good parameters in every such shrinking dilation band, for each sign. For a fixed center the same estimate holds with the directional integrand of (1) and without the factor \(2|E|\). This version explains why a construction with a summable one-sided density deficit at even one point cannot avoid all the affine copies. Related logarithmic perimeter functionals occur in [Liu–Wu–Xiao–Yuan, *The logarithmic Sobolev capacity*](https://doi.org/10.1016/j.aim.2021.107993).

## 2. Complexity of the normalized finite blocker

We use the notation \(p,M,d,\kappa,g,r_0\) of [Iosevich–Yavicoli §9.1](https://arxiv.org/html/2611.02454v1#S9.SS1) for the OpenAI hitting tree. The finite tree analysis in §§4–8 is used as given. We make explicit the following consequence.

**Quantitative blocker.** There is \(C_q\) such that for every small \(p>0\), one can choose the open periodic hitting set \(H_p\) for all \(x+tG_q\), \(1\le t\le2\), with
\[
  |H_p\cap[0,1]|\le6p,\qquad
  \log(1+J_p)\le \exp(\exp(C_q/p)),                              \tag{4}
\]
where \(J_p\) is its number of open interval components on the circle. In fact the hit can be required by index \(\exp(\exp(C_q/p))\) after enlarging \(C_q\).

Here are parameter checks. Choose \(M=1+\lceil(4\log(1/q)+4)/p\rceil\), so \(\alpha=p(M-1)/2\ge2\log(1/q)+2\). Set \(d=\lceil 2^{M-1}\log(2/p)\rceil\), ensuring the no-default probability is at most \(p/2\). Since \(\kappa\le M^{d+1}\), \(g=\lceil\log_{1/q}(8\kappa c/p)\rceil\) gives the required stability bound, with \(c=4/(1-q)\). In (7.5), \(D_{M,q}(r)\le C_q M r q^{-2r}\) for \(r\ge1\), so \(r_0=1+\lceil\log(C_qM/p)\rceil\) suffices in (9.4) by \(r e^{-2r}\le e^{-r}\). The span recurrence (4.1) bounds the largest test index \(T\) by
\[
            n_0+C(2M)^d(r_0+g+1)
\]
with an absolute \(C\): for heights \(h\ge2\), \(g+\sigma_{h-1}\ge r_0\), so \(\sigma_h=2M\sigma_{h-1}+(3M-1)g\). Thus \(T\le\exp(\exp(C_q/p))\) on increasing \(C_q\). The finest grid has \(N=2^{\lceil\log_2(cq^{-T})\rceil}\) atoms per period, and \(\log N=O_q(T)\).

The random set \(B\) is a union of its finest half-open cells. For every realization take \(B^+\) to be the union of the interiors of their enlargements of radius \(p/(4N)\), using at most \(N\) open arcs on the circle. Its extra measure is at most \(p/2\). The bad center set \(R\) is the projection onto \(x\in[0,1]\) of
\[
 \{(x,t)\in[0,1]\times[1,2]:x+tq^n\notin B^+
                   \text{ for every test index }n\}.
\]
All changing boundaries in this rectangle are lines \(x+tq^n=a\) for the lifted arc endpoints \(a\) in \([0,3]\). There are \(O(TN)\) such lines, including the rectangle's boundary lines. A line arrangement with \(L\) lines has \(O(L^2)\) faces counting all dimensions (insert its lines in order, each creating at most \(L+1\) segments). The closed failure set is the union of the closures of its selected faces: membership is constant on a face, and its closure stays in the closed failure set. Each face closure has an interval or point as its \(x\)-projection. Hence \(R\) is the union of at most \(K=O((TN)^2+1)\) closed circle intervals, counting singleton pieces. This count does not require lower bounds on the spacing of the real endpoints.

The selection argument of §9.2 gives one realization with \(\rho(B^+)+\rho(R)\le5p\), since the chosen enlargement stays within its permitted budget. Enlarge each of those closed intervals by radius \(p/(4K)\) and take the open union \(V\). Then \(\rho(V)\le\rho(R)+p/2\) and \(H_p=B^+\cup V\) satisfies the measure bound in (4). The resulting number of components is at most \(N+K\), whose logarithm is \(O_q(T)\). For \(x\notin R\), a finite test index gives a hit, as in the original argument. For \(x\in R\), the uniform radius \(p/(4K)\) guarantees a hit at any index \(n\) such that \(2q^n<p/(4K)\); one such \(n\) is \(O_q(T+\log(1/p))\). This proves also the finite horizon version of (4).

## 3. From complexity to the translation modulus

For \(j\ge0\), put \(p_j=\eta 2^{-j}/48\) and form
\[
     U_j^{\rm open}=2^{-j}(H_{p_j}\cup(-H_{p_j})),\qquad
     E=[0,1]\setminus\bigcup_{j\ge0} U_j^{\rm open}.
\]
The sets \(U_j^{\rm open}\) have periods \(2^{-j}\) dividing 1, hence their total lost measure per unit interval is at most \(12\sum p_j=\eta/2\). Every dilation of absolute value at most 2 is covered by one band \([2^{-j},2^{1-j}]\), with reflection available. A larger dilation can be made at most 2 by taking a tail of the progression, so \(E\) avoids all signed copies. This does not require \(q\) to be dyadic.

If a one-periodic open set consists of \(J\) arcs per period and has density \(v\), its symmetric difference with its translate by \(h\) has measure at most \(\min(2v,2J|h|)\) per period. This follows by separately bounding the two sets by their measures and bounding the contribution of each arc by \(2|h|\). The stage \(j\) has at most \(J_j=2^{j+1}J_{p_j}\) arcs per unit interval; touching the endpoints of the final cut \([0,1]\) adds at most \(2|h|\). Consequently
\[
 \begin{split}
 D_E(h)&\le 2|h|+
         \sum_{i\ge0}\min(24p_i,2J_i|h|).                      \tag{5}
 \end{split}
\]
Choose \(A=A(q)\) large enough that
\[
      V_j=\exp(\exp(A/p_j)),\qquad h_j=e^{-V_j}
\]
satisfy \(\log(1+J_j)\le V_j/4\) for every \(j\), using (4). The extra term \(j\log 2\) is absorbed because \(1/p_j\ge48\,2^j\). For the next bound write \(P=1/p_{j-1}\ge48\,2^{j-1}\); then \(p_j=1/(2P)\) and \(j+1\le P\). For \(A\ge1\) we have \((3/4)V_{j-1}\ge3P>\log(4(j+1)P)\), so \(2(j+1)e^{-3V_{j-1}/4}\le p_j\).

For \(h_j<|h|\le h_{j-1}\), the contribution to (5) of the first \(j\) stages and of the boundary is at most \(p_j\) by the last bound, since \(J_i\le e^{V_{j-1}/4}\) for \(i<j\). The tail contributes at most \(24\sum_{i\ge j}p_i=48 p_j\). Finally \(\log\log\log(1/|h|)\le A/p_j\) in the same range. Multiplying proves (2).

For example, put \(\Lambda(h)=\log\log\log(1/h)\) for \(0<h<h_0\) sufficiently small. The sets just constructed have finite weighted seminorm
\[
              \int_0^{h_0} D_E(h)\,(-d(\Lambda(h)^\beta))<\infty
                     \qquad(0<\beta<1);
\]
indeed the integral is bounded by a constant times \(\int_{\Lambda(h_0)}^\infty u^{\beta-2}\,du\). At the much stronger Dini weight \(dh/h\), divergence is unavoidable by (1). No sharp boundary between these regularity statements is asserted.

The companion [exact fixture verifier](verify_factor_similarity_translation_regularity.py) computes finite bad-center projections by rational polygon clipping and checks annulus changes and interval-translation bounds on small rational fixtures. It does not enumerate the astronomical finite trees of the existence proof or replace its analytic estimates.
