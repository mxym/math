# Sharp regularity for correlated linear sources in a split-ring hash

The counting-ideals leftover hash lemma gives an exact collision quantity and an upper bound on total variation for much more general sources. For a **uniform affine linear source** in a product of equal finite fields, the actual total variation has a different sharp leading term. A hyperplane calculation keeps rare multi-relation clusters from being counted multiple times.

## 1. Model and guarantee

Let \(F=\mathbb F_q\), let \(W\subseteq\bigoplus_{a=1}^g F^{m_a}\) be a linear subspace, and take the source uniform on an affine coset of \(W\). Its coordinates in different factors need not be independent. In factor \(a\), draw a uniform \(k_a\)-by-\(m_a\) matrix \(B_a\) over \(F\), independently across factors and of the source. Set \(K=\sum_a k_a\ge1\). Compare the joint law of the public seed \(B=(B_a)\) and the \(K\) output symbols to the same seed followed by independent uniform \(F^K\); denote its total variation by \(\mathcal D_q\).

This includes the public uniform ring-linear hash with \(q\) a completely split prime, so the quotient ring is a product of copies of \(F\), provided the source is uniform on such an affine \(F\)-subspace. It is not a statement about a deployed scheme, arbitrary nonlinear sources, or a hidden seed.

Each output row pulls back to an independent uniform vector \(Y_i\) in a subspace \(V_i\subseteq W^*\), for \(i=1,\ldots,K\): \(V_i\) is the image of the corresponding factor's dual coordinate projection, repeated if that factor has multiple output rows. For any index set \(I\), let \(V_I=\sum_{i\in I}V_i\), and for \(I\ne\varnothing\) set \(s(I)=\dim V_I-|I|\). Full rank is possible exactly when all \(s(I)\ge0\). If not, \(\mathcal D_q\ge1-1/q\). In the full-rank-possible case use the following definitions.

Fix any order of the rows. For \(i\in I\subseteq[i]\), let \(\gamma_{i,I}=1\) if there exists a linear functional \(\ell\) on \(V_{[i]}\) with
\[
 \{j\le i:\ell|_{V_j}=0\}=I,
 \qquad
 \text{independent representatives exist for }V_j\cap\ker\ell,\ j<i .
\]
Otherwise put \(\gamma_{i,I}=0\). The zero functional is allowed (then \(I=[i]\)). The independent-representative condition means one vector from each indicated subspace, and can equivalently be expressed by the ordinary Rado rank inequalities on these cut subspaces. Define
\[
 S_q=\sum_{i=1}^K\ \sum_{i\in I\subseteq[i]}
                  \gamma_{i,I}\,q^{-s(I)-1}.
\]
For all these sources,
\[
 \boxed{\quad
   (1-3K/q-1/q)_+\,S_q\ \le\ \mathcal D_q\ \le\ S_q .
 \quad}                                                        \tag{1}
\]
The multiplicative estimate is uniform in all ambient dimensions and arrangements. In particular it is sharp as a relative estimate if \(K=o(q)\). For fixed \(K\), put \(s_*=\min_{I\ne\varnothing}s(I)\), and let \(b_q\) count the displayed pairs \((i,I)\) with \(\gamma_{i,I}=1\) and \(s(I)=s_*\). Then
\[
          \mathcal D_q=b_q\,q^{-s_*-1}+O_K(q^{-s_*-2}),\qquad
          1\le b_q\le 2^K-1                                     \tag{2}
\]
for all sufficiently large \(q\), with \(b_q\) independent of the chosen row order then. The arrangement may depend on \(q\); the formula specifies its leading coefficient without a general-position assumption.

## 2. First dependence and a clipped-transversal count

The affine shift changes no conditional distance. Given the rows, the output is uniform on an affine subspace of dimension their rank. If \(\delta=K-\operatorname{rank}(Y_1,\ldots,Y_K)\), its total variation from uniform is \(1-q^{-\delta}\). Thus
\[
 (1-q^{-1})\Pr(\delta>0)\le \mathcal D_q\le\Pr(\delta>0).
\]
For independent representatives of the original \(V_i\), Rado's condition follows by induction: if a nonempty proper subset is tight, choose its representatives and quotient by their span, preserving the inequalities on the remaining sets. If there is no such tight subset, choose a nonzero vector in the last subspace and quotient by its line; all proper nonempty sets on the remaining indices can lose at most one dimension and still meet the inequalities. Necessity is immediate. This also justifies the same interpretation on the cut subspaces.

Let \(E_i\) be the event that the first dependence is at row \(i\). On previous independence the span \(H\) of the old rows has dimension \(i-1\). With \(D_i=\dim V_{[i]}\),
\[
 \Pr(Y_i\in H\mid H)
 = q^{-(D_i-i+1)}
   \big|\{\ell\in V_{[i]}^*:\ell(H)=0,\ \ell(V_i)=0\}\big|.      \tag{3}
\]
Indeed the left side is \(q^{-\dim (V_i/(H\cap V_i))}\) and the dual count is \(q^{D_i-\dim(H+V_i)}\).

Partition the functionals of (3) according to the exact set \(I=\{j\le i:\ell(V_j)=0\}\), which always contains \(i\). For any fixed such \(\ell\), the probability all old rows are in \(\ker\ell\) is \(q^{-(i-|I|)}\) by independence and uniformity. Conditional on that event, the old rows are independent uniform vectors in the cut subspaces \(V_j\cap\ker\ell\). Let \(p_\ell\) be their probability of linear independence under that conditional law. Then
\[
   \Pr(E_i)=\sum_{i\in I\subseteq[i]}
        q^{|I|-D_i-1}\sum_{\ell\text{ of exact type }I}p_\ell.    \tag{4}
\]

Here are uniform bounds on each inner sum. If \(\gamma_{i,I}=0\) it is zero. If \(\gamma_{i,I}=1\), choose one good \(\ell_0\) and independent representatives \(w_j\in V_j\cap\ker\ell_0\), \(j<i\). For each \(j\notin I\) choose a vector \(u_j\in V_j\) with \(\ell_0(u_j)\ne0\). On the linear space
\(L_I=\{\ell:\ell(V_I)=0\}\), use
\[
 w_j(\ell)=
 \begin{cases}
    w_j & j\in I,\\
    \ell(u_j)w_j-\ell(w_j)u_j & j\notin I.
 \end{cases}
\]
These are in the required cut subspaces for every \(\ell\in L_I\). A nonzero independence minor at \(\ell_0\), multiplied by the factors \(\ell(u_j)\) for \(j\notin I\), is a polynomial of degree at most \(2(i-|I|)\) that is nonzero at \(\ell_0\). Its nonzeros witness both exact type \(I\) and a good independent selection. By the elementary polynomial zero bound over \(F\), at least a \(1-2(i-|I|)/q\) fraction of the \(q^{D_i-\dim V_I}\) possible \(\ell\)'s are good, or the bound is trivial when negative. This includes the zero-dimensional \(L_I\) case, where the successful polynomial is constant.

For each good \(\ell\), an independence minor expressed on independent uniform coordinates in the cut subspaces is a nonzero polynomial of total degree at most \(i-1\), by the same existence witness. Thus \(p_\ell\ge1-(i-1)/q\). Multiplying the two lower bounds and using \(p_\ell\le1\) gives
\[
 (1-3K/q)_+\gamma_{i,I}q^{D_i-\dim V_I}
       \ \le\ \sum_{\ell\text{ of exact type }I}p_\ell
       \ \le\ \gamma_{i,I}q^{D_i-\dim V_I}.
\]
Sum (4) over disjoint first-dependence events to get (1). To see (2), the nonminimum-slack terms together are \(O_K(q^{-s_*-2})\). Choose a row order that puts any minimum-slack subset as an initial prefix; the pair at the end of that prefix with \(\ell=0\) contributes one. The event probability is independent of order; comparing (2) for two orders, their integer leading coefficients differ by \(O_K(1/q)\), hence agree for sufficiently large \(q\). This also proves positivity for any order in that range.

## 3. Tight arrangements: a purely rank-function coefficient

When \(s_*=0\), the leading coefficient simplifies. Let \(\mathcal T\) consist of the empty set and every tight set \(J\) with \(s(J)=0\); write \(T\) for the union of all of them. By submodularity of subspace-sum dimension and nonnegativity of slack, \(\mathcal T\) is closed under union and intersection. If
\[
       \varnothing=T_0\subsetneq T_1\subsetneq\cdots\subsetneq T_\ell=T
\]
is any maximal chain of tight sets, then for fixed \(K\)
\[
                       \mathcal D_q=\ell/q+O_K(q^{-2}).         \tag{5}
\]
Indeed, conditional on full rank on \(T_{j-1}\), the rows of that set span exactly \(V_{T_{j-1}}\). In the quotient by this predetermined subspace, the incremental block \(T_j\setminus T_{j-1}\) is tight and every nonempty proper subset has strictly positive slack, by maximality of the chain. In such a block the only zero-slack pair in (2) is the complete block at its last row, with the zero functional, so its conditional failure probability is \(1/q+O_K(q^{-2})\). Multiplying the stage successes gives the coefficient in (5) on \(T\). Any additional dependency uses a support \(I\not\subseteq T\) and then \(s(I)\ge1\). For a fixed projective coefficient vector with support \(I\), the linear combination of independent rows is uniform on \(V_I\), so has zero probability \(q^{-\dim V_I}\). There are \((q-1)^{|I|-1}\) such projective vectors; a union bound contributes only \(O_K(q^{-2})\) outside \(T\). The conditional distance and failure probability already differ by at most a relative \(1/q\).

Equivalently \(\ell\) is the number of equivalence classes of indices in \(T\) that belong to exactly the same tight sets. The inclusion implications between these classes give a partial order; any down-set is the union of the minimal tight sets containing its elements, and is tight. This identifies the tight sets with the order ideals of that partial order, so every maximal chain adds each class exactly once.

## 4. Why collision is not the leading TV coefficient

The exact order-two likelihood moment of the same joint law is \(\mathbb E q^\delta\): conditionally on the seed, the density with respect to uniform is \(q^\delta\) on a proportion \(q^{-\delta}\) of the outputs. The excess moment also equals the expected number of nonzero relations,
\[
     \mathbb E(q^\delta-1)=
       \sum_{I\ne\varnothing}(q-1)^{|I|} q^{-\dim V_I}.
\]
This identity counts **all** dependence vectors, while approximation in TV counts their rank failures without this multiplicity. For fixed \(K\), its leading scale is \(q^{-s_*}\), not \(q^{-s_*-1}\). Even dividing the number of nonzero relations by \(q-1\) does not generally give the leading failure coefficient.

For an elementary example let \(V_i=\operatorname{span}\{e_0,e_i\}\) in dimension \(K+1\), with one independent row in each \(V_i\). All nonempty subsets have the same slack 1. A row has form \(a_i e_0+b_i e_i\); the rows with \(b_i\ne0\) are independent on their distinct coordinates, and the rows with \(b_i=0\) together have rank zero or one on \(e_0\). Failure first occurs either by a zero row, of leading probability \(K q^{-2}\), or by two nonzero rows on \(e_0\), of leading probability \(\binom K2 q^{-2}\). Their overlaps and three or more such rows are \(O_K(q^{-3})\). Thus the leading coefficient of the actual TV is \(K+\binom K2\), whereas the expected number of projective relations has coefficient \(2^K-1\). For \(K=3\) these are respectively 6 and 7. The extra coefficient comes from a rare cluster, not a new single failure.

## Relationship to earlier results

[Boudgoust and Lapiha, *Leftover Hash Lemma(s) Over Cyclotomic Rings*](https://opencryptology.org/2025/1080/versions/20260428T172000Z.pdf), Theorem 4, give an exact Rényi-2 expression by counting ideals and a general TV upper bound, covering arbitrary sources and rings outside this model. Their Lemma 23 gives a finite-field product rank bound in the full-module source setting. Here we specialize to an affine-linear source, allow dependencies across split factors, and evaluate the actual asymptotic TV with a uniform finite-field multiplicative guarantee. This does not replace their general lemma. The existence of independent representatives itself is classical [Rado](https://doi.org/10.1093/qmath/os-13.1.83); the calculation above concerns random selection probabilities, not an implementation or a search for hidden information. The accompanying verifier checks synthetic arrangements and the exact first-failure identity on small fields.
