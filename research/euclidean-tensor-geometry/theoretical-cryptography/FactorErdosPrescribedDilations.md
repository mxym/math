# Prescribed-dilation avoidance in the Erdős similarity problem

**Catalogue #097 / Erdős problem [#120](https://www.erdosproblems.com/120).** For every bounded infinite pattern, one high-density compact set can avoid all translations at almost every nonzero dilation with respect to each of a prescribed countable family of measures, without any Fourier-decay assumption on these measures. Separately, a Hausdorff-gauge criterion on a *prescribed set of dilations* gives pointwise avoidance at every dilation in that set. It yields explicit gauges for \(2^{-n^2}\) and \(2^{-2^n}\). Neither result proves that either fast sequence can be avoided at **all** nonzero dilations.

For a pattern \(A\subset\mathbb R\), an avoiding set \(E\) and \(t\ne0\), consider the property
\[
\tag{1}
\text{for every }x\in\mathbb R,\quad (x+tA)\setminus E
\text{ contains infinitely many distinct points.}
\]
Let \(\rho\) denote the Haar probability on \(\mathbb T=\mathbb R/\mathbb Z\), or the corresponding density of a \(1\)-periodic set. We give closed periodic \(E\); intersecting with \([0,1]\) only strengthens (1). In every statement the measure in any unit interval exceeds \(1-\eta\), for an arbitrary prescribed \(\eta>0\). Adjoining an open dense periodic set of arbitrarily small density to the deletion set makes \(E\) nowhere dense, if desired.

## 1. A finite interval-of-scales bound

Fix a finite accumulation point \(a_*\) of \(A\). Take distinct nonzero \(b_1,\ldots,b_m\) with \(a_*+b_i\in A\), \(r=\max_i|b_i|\), and \(s=\min_{i\ne i'}|b_i-b_{i'}|>0\), where \(m\ge2\). Fix \(0<a\le b<\infty\), with \(2br\le1/4\) and \(as\le1\). Set
\[
q=\left\lceil\frac{2}{as}\right\rceil,\qquad w=\frac1q,\qquad
\delta=\frac{w}{2r}.
\]
Suppose the scale set \(F\subset\{a\le|t|\le b\}\) is covered by \(M\) intervals of length at most \(\delta\). For any \(0<p<1\) and \(\epsilon>0\), there exists an open periodic deletion set \(H\) such that
\[
\tag{2}
\rho(H)\le 3p+M e^{-pm}+\epsilon .
\]
For each \(x\in\mathbb R\) and \(t\in F\), this \(H\) either meets the finite copy of the displayed \(m\) points or contains an open neighborhood of its accumulation center \(x+t a_*\).

To prove this, on the circle color the \(q\) half-open cells of length \(w\) independently with probability \(p\). For a colored cell \([kw,(k+1)w)\), include the open interval \(((k-1)w,(k+2)w)\) modulo \(1\) in \(B^+\). Then \(\mathbb E\rho(B^+)\le3p\). Use one representative \(t_I\) from \(F\cap I\) in each nonempty covering interval and replace \(F\) for this proof by the finite union \(F'=\bigcup_I\overline{F\cap I}\). This union is compact and remains in the same annulus, even if \(F\) was not measurable.

For a fixed center \(y\) and \(t_I\), the \(m\) points \(y+t_I b_i\bmod1\) occupy distinct cells: their pairwise circular distances are their absolute differences, between \(as\) and \(2br\). If one of those cells is colored, the corresponding point \(y+t b_i\) belongs to \(B^+\) for every \(t\in\overline{F\cap I}\), since its displacement is at most \(r\delta=w/2\). Thus the probability that \(y\) has even one \(t\in F'\) for which all tests miss \(B^+\) is at most \(M(1-p)^m\). The set \(R\) of these centers is the projection of a closed subset of the compact \(\mathbb T\times F'\), so it is closed. Averaging \(\rho(B^+)+\rho(R)\) selects a realization with total at most \(3p+Me^{-pm}\). Cover \(R\) by an open periodic \(V\) with extra density at most \(\epsilon\) and take \(H=B^+\cup V\). For centers in \(R\), the neighborhood \(V\) catches arbitrarily late points of the affine image of the accumulating subset of \(A\). For centers outside \(R\), at least one of the finite tests succeeds. This proves (2), including every center and both signed annuli.

## 2. Hausdorff measures on prescribed sets of scales

**Theorem A (mesh-gauge criterion).** Choose for each \(j\ge1\) a block of \(m_j\ge2\) nonzero offsets in \(A-a_*\), with maximum absolute value \(r_j\to0\) and minimum pairwise gap \(s_j>0\). Let \(\delta_j\downarrow0\) strictly with
\[
\tag{3}
0<\delta_j\le s_j/(16j r_j).
\]
Choose \(p_j\in(0,1)\) with \(\sum_j p_j<\infty\) and \(\Gamma_j=p_jm_j\) eventually nondecreasing and tending to infinity. For sufficiently small positive \(u\) define the nondecreasing gauge
\[
\tag{4}
h(u)=\exp(-\Gamma_j/2)\quad(\delta_{j+1}<u\le\delta_j).
\]
Every prescribed \(T\subset\mathbb R\setminus\{0\}\) contained in a countable union of sets of finite \(h\)-Hausdorff outer measure admits a single high-density closed periodic \(E\) satisfying (1) for all \(t\in T\). A nondecreasing gauge tending to zero, not necessarily continuous, is enough: we use countable interval covers with the scale limit in the usual definition. We set \(h(0)=0\); singleton members of a cover can equivalently be thickened with arbitrarily small total extra cost.

**Proof.** It suffices first to cover the case \(T\subset\{a\le |t|\le b\}\) with \(L=\mathcal H^h(T)<\infty\). At each sufficiently late \(j\), both separation conditions of §1 hold. Moreover \(w_j\ge as_j/(2+as_j)\ge as_j/3\). Thus \(w_j/(2r_j)\ge as_j/(6r_j)>\delta_j\) once \(aj\ge1\). With arbitrary sufficiently large \(J\), cover \(T\) by intervals of positive lengths at most \(\delta_J\) and total \(h\)-cost at most \(L+1\). Use closed intervals, by replacing each covering set by its convex hull and thickening any singleton separately. Group these intervals according to \(\delta_{j+1}<|I|\le\delta_j\); the group size \(M_j\) is finite and \(\sum_{j\ge J} M_j\exp(-\Gamma_j/2)\le L+1\).

Apply (2) once for each nonempty group, with \(p=p_j\), the block at \(j\), and regularity errors summing to at most \(\epsilon\). We need not pay the coloring density separately for every interval within a group. Their union \(H_J\) is open periodic and has
\[
\tag{5}
\rho(H_J)\le3\sum_{j\ge J}p_j+(L+1)\sup_{j\ge J}\exp(-\Gamma_j/2)+\epsilon .
\]
Both displayed tail terms tend to zero. For any scale \(t\in T\) and center \(y\), the deletion either catches a finite point with nonzero offset bounded by \(\sup_{j\ge J}r_j\), or contains a neighborhood of \(y\). In the latter case it also catches nonzero offsets arbitrarily close to zero. Choose a sequence \(J_k\to\infty\) and errors so that the bounds in (5) are summable with arbitrarily small total. The complement of the union of the \(H_{J_k}\) then satisfies (1), because the blocked nonzero offsets can be chosen to tend to zero. Countably many annuli and finite-measure pieces are handled by intersecting their avoiding sets with summable density losses. ∎

Without a growth requirement on \(A\), this gives at least one gauge tending to zero for every infinite bounded \(A\): take \(m_j=2^j\), \(p_j=(j+1)^{-2}\), arbitrary \(m_j\) distinct nearby points, and decrease \(\delta_j\) further if needed to make it strictly decreasing. Countable sets of nonzero dilations, in particular, always satisfy the criterion.

### Two fast-decay examples

**Corollary.** Put \(S=\log(1/u)\). For each \(c>0\) and \(\varepsilon>0\), the respective following gauges (defined for sufficiently small \(u>0\)) satisfy the conclusion of Theorem A for the indicated patterns:
\[
\begin{array}{c|l}
A & g(u)\\ \hline
\{2^{-n^2}:n\ge1\}
& \exp\!\bigl[-c\sqrt S/(\log S)^{1+\varepsilon}\bigr]\\
\{2^{-2^n}:n\ge1\}
& \exp\!\bigl[-c\log S/(\log\log S)^{1+\varepsilon}\bigr].
\end{array}
\]
In particular, every prescribed \(\sigma\)-finite \(\mathcal H^g\) set of dilations is excluded pointwise with all translations, not just almost everywhere with respect to a measure on that set.

To check the estimates, use \(m_j=2^j\) consecutive terms starting at \(n=j\), \(r_j=a_j\), and \(s_j=a_{j+m_j-2}-a_{j+m_j-1}\). The last pair is the minimum, because \(a_{n+1}\le a_n/2\) makes the consecutive differences decreasing. Also \(a_{j+m_j-2}/2\le s_j\le a_{j+m_j-2}\). Choose \(\delta_j=\min\{s_j/(16j r_j),\delta_{j-1}/2\}\) (omit the second term initially). For the square exponents \(\log(1/\delta_j)\asymp4^j\); for the double exponential \(\log\log(1/\delta_j)\asymp2^j\). For example, before the minimum with \(\delta_{j-1}/2\), the latter logarithm is \((j+2^j-2)\log 2+O(1)\), and the former logarithm in the square case is \(((j+2^j-2)^2-j^2)\log2+O(\log j)\). Taking the minimum only replaces \(\log(1/\delta_j)\) by the running maximum of these raw logarithms plus at most \(j\log2\), preserving the estimates.

For \(u\) in band \(j\) of (4), in both examples the displayed exponent \(\log(1/g(u))\) is bounded above by \(C_{c,\varepsilon}2^j/(j+1)^{1+\varepsilon}\). Choose \(p_j=D/(j+1)^{1+\varepsilon}\) for all sufficiently large \(j\) with \(D>2C_{c,\varepsilon}\); adjust finitely many earlier terms to lie in \((0,1)\). Then \(g(u)\ge h(u)\) for small \(u\), so finiteness for \(\mathcal H^g\) implies finiteness for \(\mathcal H^h\). ∎

The gauges decrease much more slowly than any positive power of \(u\), so their \(\sigma\)-finite sets have Hausdorff dimension zero. They can nonetheless be uncountable. For example the compact set
\[
T=1+\Big\{\sum_{k\ge1}\epsilon_k2^{-D_k}:\epsilon_k\in\{0,1\}\Big\},\qquad D_k=2^{k^2},
\]
has zero measure for every gauge in the corollary, by covering with \(2^k\) intervals of length at most \(2^{1-D_{k+1}}\). The binary coding is injective by domination of each digit over its tail. For the slower-decaying gauge (the double-exponential-pattern row), the absolute logarithm of the gauge of that length is bounded below by a positive constant times \(k^2/(\log k)^{1+\varepsilon}\), which dominates \(k\); the other row is even smaller there. Also \(2^{D_k}t\bmod1\to0\) uniformly on \(T\). Thus every nonzero finite positive measure supported by \(T\) has Fourier coefficients tending to its total mass along \(2^{D_k}\), not to zero. A result testing only measures with Fourier decay cannot by that test alone preclude any particular dilation of \(T\).

### Why the variable-radius hypothesis is not a common-mesh box criterion

For each one of these two gauges \(g\) there even exists a compact \(T\subset[1,2]\) of zero \(\mathcal H^g\) such that every nonempty relatively open subset of \(T\) has lower box dimension \(1\). In particular such a \(T\) need not be a countable union of subsets having \(\liminf_j m_j^{-1}\log N_{\delta_j}=0\), where \(N_u\) counts intervals of length \(u\) needed to cover the subset and \(m_j,\delta_j\) are those used above.

Here is an elementary construction for any such gauge tending to zero. In each interval node \([v,v+\ell]\) use \(v\) as its center, and put pairwise-disjoint closed child intervals with left endpoints \(v+d_n\), where \(d_n=\ell/(4\log(n+2))\), \(n\ge1\), and with lengths positive and at most half the neighboring endpoint gaps. Make the lengths small enough that at generation \(k\) they are at most \(2^{-k}\) and their total \(g\)-cost is at most \(2^{-k}\); this is possible because there are only countably many nodes at each finite generation. Start from \([1,2]\). At each generation the union of current intervals and all earlier centers is compact: if the child index is unbounded at the first diverging level of a sequence, the sequence converges to that parent's center; otherwise extract a subsequence fixing successive child indices up to the finite generation, or an earlier center. Their nested intersection \(T\) is compact. The countably many centers have zero \(\mathcal H^g\), and the other points are covered by the generation-\(k\) intervals at cost \(2^{-k}\), so \(\mathcal H^g(T)=0\).

Any neighborhood of a point of \(T\) contains a whole descendant interval (or a child interval near a center), and thus contains one scaled skeleton of centers \(d_n\). For \(n\le u^{-a}\) with any fixed \(0<a<1\), the consecutive skeleton gaps are bounded below by a constant times \(u^a/(\log(1/u))^2\), greater than \(u\) for all small \(u\). Indeed the derivative of \(1/\log(x+2)\) has magnitude \(1/((x+2)(\log(x+2))^2)\). Therefore each nonempty relatively open subset has lower box dimension \(1\). Were \(T\) covered by countably many subsets with the stipulated common-mesh \(\liminf\), Baire's theorem would put a relatively open subset of \(T\) in one of their relative closures. Taking the closure does not increase the number of length-\(u\) closed intervals in a finite cover. But \(\log(1/\delta_j)/m_j\to\infty\) for both patterns, contradicting the property of that relatively open subset. This example concerns Hausdorff versus common-mesh entropy, independently of the explicit Fourier example above.

## 3. Almost every scale for an arbitrary prescribed measure

**Theorem B (prescribed measures).** For every bounded infinite \(A\) and every countable family \((\nu_i)\) of finite positive Borel measures on \(\mathbb R\), there exists a single high-density closed periodic \(E\) such that for every \(i\), (1) holds for \(\nu_i\)-almost every \(t\ne0\). In fact it can be made to hold at every nonzero atom of every \(\nu_i\).

**Proof.** Combine the measures into \(\nu=\sum_{i\ge1}2^{-i}\nu_i/(1+\nu_i(\mathbb R))\), and let \(\nu_0\) be its atomless part. The nonzero atoms are countable and handled pointwise by Theorem A; it remains to make a separate deletion set for \(\nu_0\)-almost every scale simultaneously for every center.

Take any aperture \(\vartheta\in(0,1/8)\). On the circle choose finitely many open arcs \(I_\ell\) such that every open arc of length \(\vartheta\) contains one of them, for example a sufficiently fine mesh of centers with arc lengths \(\vartheta/4\). There are nonnegative real trigonometric polynomials \(P_\ell\) satisfying \(P_\ell\ge1\) off \(I_\ell\) and \(\int_{\mathbb T}P_\ell<1\). To see this, subtract a nonzero nonnegative continuous bump bounded by \(1/2\) and supported in \(I_\ell\) from the constant \(1\). Approximate the resulting continuous function uniformly by a Fejér polynomial and add the approximation error, taken smaller than half the mean of the bump. Let \(R\ge1\) bound all the Fourier degrees, and \(\mu<1\) bound all the means.

Select \(m\) offsets \(b_i\) from \(A-a_*\), nonzero and of magnitudes decreasing geometrically so that \(|b_{i+1}|\le |b_i|/(2R+2)\). This is possible inside any prescribed punctured neighborhood of zero. The first nonzero term in any sum \(\lambda=\sum_i k_i b_i\), with integers \(|k_i|\le R\), dominates the sum of all later absolute values, so \(\lambda\ne0\) unless all \(k_i=0\). For a positive integer \(q\), delete the single family of periodic open holes
\[
H_q=\{z:\operatorname{dist}(qz,\mathbb Z)<\vartheta/2\},\qquad \rho(H_q)=\vartheta .
\]
If at some center \(y\) all \(y+t b_i\) miss \(H_q\), then all \(qt b_i\bmod1\) miss a common arc of length \(\vartheta\), and hence one of the \(I_\ell\). The resulting explicit bad-scale set \(B(q)\) is the union over \(\ell\) of these latter miss conditions for every \(i\). It satisfies
\[
\tag{6}
\nu_0(B(q))\le \sum_\ell\int\prod_{i=1}^mP_\ell(qt b_i)\,d\nu_0(t).
\]
For every \(\lambda\ne0\), the Cesàro mean in positive integers \(q\) of \(\exp(2\pi i q\lambda t)\) tends to zero unless \(\lambda t\in\mathbb Z\). The exception is countable, hence \(\nu_0\)-null; dominated convergence proves that the mean of its integrals tends to zero. In the finite Fourier expansion of each product of (6) only the all-zero frequency survives. Consequently the Cesàro mean of the right side of (6) tends to at most \(\#\{\ell\}\nu_0(\mathbb R)\mu^m\). Choose \(m\) large enough that this is smaller than any specified positive threshold. Some (indeed arbitrarily large) integer \(q\) then has \(\nu_0(B(q))\) smaller than that threshold, with no Fourier-decay assumption on \(\nu_0\).

Repeat with summable apertures of arbitrarily small total, summable thresholds, and blocks of nonzero offsets shrinking to zero. Borel–Cantelli says that \(\nu_0\)-almost every \(t\) lies in only finitely many bad-scale sets \(B(q_j)\). For each such \(t\) and **every** \(y\), all sufficiently late stages delete a point with nonzero offset from the \(j\)-th block. These give infinitely many distinct points. Intersect with the high-density set excluding all nonzero atoms to finish. For compact \([0,1]\) avoidance of an unbounded pattern one does not need this argument: every nonzero affine copy remains unbounded. ∎

By intersecting with the set constructed in Theorem A, the same \(E\) can satisfy both Theorem B and any of the exact-scale conclusions above. Theorem B also applies to a countable family of \(\sigma\)-finite Borel measures: replace each one by an equivalent finite measure, weighting a countable finite-measure partition by positive summable normalized weights. Similarly, countably many prescribed patterns (each paired with its own admissible scale sets or measures) can be handled at once by summable density budgets.

## Prior work and scope

- [Kolountzakis, *Infinite patterns that can be avoided by measure* (1997)](https://doi.org/10.1112/S0024609397003056) proves avoidance at Lebesgue-almost every scale and supplies classical random-cell arguments. [Chlebík, *On the Erdős similarity problem*](https://arxiv.org/abs/1512.05607) and [Kovač, *Superexponentially decaying sequences in the Erdős similarity problem*, Lemma 4](https://hexagonmath.org/pdf/2610.00176v1) use related cell and center repair ideas; the latter uses a single normalized-gap scale and later a branching refinement for all scales under a different hypothesis. Theorem A counts arbitrary prescribed covering intervals by their length bands and uses a single random coloring budget in each band. Chlebík's Theorem 12 treats prescribed measures on the **pair** space, allowing exceptional translations even at good scales; in (1) there are no exceptional translations at a good scale. His Theorem 13 treats \(\sigma\)-finite \(\mathcal H^1\) subsets of the pair space; for uncountable \(T\), a full product interval \(\times T\) is not such a subset, as every vertical fiber has positive length and a finite-measure piece can meet at most countably many fibers in positive length.
- [Kulkarni–Mora Cuéllar, *Exceptional parameters in the Erdős similarity problem*](https://arxiv.org/abs/2611.15734), Lemmas 2.1–2.3 and Theorems 1.1–1.3, uses the lacunary Fourier product majorant employed in Theorem B. Its Theorem 1.1 handles uncountable classes of measures with specified pointwise decay moduli, whereas ours handles countably many **specified individual measures**, with no pointwise decay. It does not replace the former uniformity. Their Hausdorff theorem bounds the gauge measure of the exceptional set arising from their construction; Theorem A instead disjoins the exceptional set from a **prescribed** set of scales.
- [OpenAI's geometric-case proof](https://github.com/openai/math/tree/main/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026), [Jiang–Xi](https://arxiv.org/abs/2610.11449) and [the repository's growing-gaps preprint](https://doi.org/10.5281/zenodo.23305280) prove all-scale results for other pattern hypotheses. The repository's [thin-burst refinement](https://github.com/mxym/math/blob/31cb661a6fe7a53c6d83b464fba5e0e0799a9039/research/euclidean-tensor-geometry/theoretical-cryptography/FactorErdosSimilarityThinBursts.md) likewise concerns filled logarithmic bursts and controls a family of powers via local tree entropy, rather than prescribed dilation measures for arbitrary bounded patterns. Here the growth of the logarithmic exponents in \(2^{-n^2}\) and \(2^{-2^n}\) is used only to quantify the restricted-scale gauge, not to obtain any all-scale conclusion. The proof is analytic and uses no numerical or computer certificate.
