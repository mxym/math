# Low-rank polar spaces give certified affine slices of quadratic weights

A common low-rank structure in explicit quadratic factor tables can be exposed without searching for a maximum-rank pencil member. The resulting affine slices can be normalized by previously verified product-factor arithmetic when their remaining independent blocks are small. All weights below are given mathematical functions; there is no sample-to-model step, key-recovery task, or claim about standard noisy equations.

## 1. A constructive common-isotropy bound over every finite field

Let \(V=\mathbb F_q^N\) and let \(\mathcal S\) be a space of symmetric bilinear forms on \(V\), presented by matrices \(M_1,\dots,M_m\). The statements also hold for a space of alternating bilinear forms, whether or not the characteristic is two. Let
\[
 R=\operatorname{rank}_{\mathbb F_q(t_1,\ldots,t_m)}
                        \biggl(\sum_j t_jM_j\biggr),\qquad
 r=\max_{t\in\mathbb F_q^m}\operatorname{rank}
                        \biggl(\sum_j t_jM_j\biggr).
\]
There is a deterministic Gaussian-elimination procedure, polynomial in the input representation, which finds \(U\subseteq V\) satisfying
\[
     B(u,u')=0\quad\text{for all }B\in\mathcal S,\;u,u'\in U,\qquad
     \operatorname{codim}U\le R\le\left\lfloor\frac{q}{q-1}r\right\rfloor.   \tag{1}
\]
It need not compute either \(R\) or \(r\), adjoin a field, or solve a symbolic determinant identity problem. Its output is a basis of a common totally isotropic subspace, not a maximum-dimension one. The bound by \(R\) for its codimension can be attained: take all coordinate diagonal forms on an \(R\)-dimensional direct summand and zero elsewhere. In the alternating-only variant with even \(R\), all alternating forms on such a direct summand force codimension at least \(R-1\), since any two independent projected vectors can be paired nontrivially by some alternating form.

### The rank budget

For any symmetric or alternating \(B\in\mathcal S\) of rank \(d\), let \(H=\operatorname{rad}(B)\) and denote by \(\mathcal S|_H\) the space of bilinear restrictions to \(H\times H\). Write \(\mathrm{grk}\) for generic rank. Then, over any field,
\[
                   \mathrm{grk}(\mathcal S|_H)+d
                         \ \le\ \mathrm{grk}(\mathcal S).                 \tag{2}
\]
To see this, choose a complement to \(H\); the restriction of \(B\) to such a complement is nonsingular because anything in its radical also pairs trivially with \(H\). In this basis \(B=B_0\oplus0\), \(\det B_0\ne0\). Let \(C(t)\) be a generic member of \(\mathcal S\), and take a square nonzero minor \(J\) of its bottom block of size \(s=\mathrm{grk}(\mathcal S|_H)\). In \(B+zC(t)\), the minor selecting the whole first block together with the bottom rows and columns of \(J\) has initial term
\[
                     z^s\det(B_0)\det(J).
\]
Indeed the last \(s\) rows each carry one \(z\); after factoring those out, setting \(z=0\) makes the matrix lower block triangular. Thus the bordered minor is nonzero over the rational function field in \(z,t\). All minors of size above \(\mathrm{grk}(\mathcal S)\) vanish identically in a generic member, and so still vanish after this substitution. This proves (2).

Start with \(U=V\). If some supplied generator remains nonzero on \(U\times U\), replace \(U\) by the radical of that restricted form, computed inside \(U\). At a step of rank \(d>0\), its dimension drops by \(d\), and (2) lowers the remaining generic-rank budget by at least \(d\). Stop when all the restricted generators vanish. Thus the total codimension removed is at most the original \(R\), regardless of which nonzero generator is chosen at each step. There are at most \(N\) steps, made up of restricting explicit matrices and ordinary elimination. Neither a search for a generic-rank witness nor a large-field assumption is needed.

### Finite-rank comparison (known)

For completeness, let \(f(t)\) be a nonzero determinant minor of order \(R\) of the generic pencil. At a specialization \(a\), constant row operations make at least \(R-\operatorname{rank}(\sum a_jM_j)\) rows of that minor vanish. The multiplicity of \(f\) at \(a\) is at least that number. The multiplicity Schwartz–Zippel bound gives \(\sum_{a\in\mathbb F_q^m}\operatorname{mult}(f,a)\le Rq^{m-1}\), hence the average specialization rank is at least \(R(1-1/q)\). This is the rank specialization argument of [A Degree–Size Relation for Resolution over Polynomials, Lemma 3.1](https://arxiv.org/html/2610.00837v1#S3.Thmlemma1), stated there for prime fields; the same argument applies over \(\mathbb F_q\). Since the average is at most \(r\), we obtain the last part of (1). This is not a claim that the field-size factor can be improved: diagonal matrices indexed by all projective nonzero linear forms on \(\mathbb F_q^m\) have \(R=(q^m-1)/(q-1)\) and \(r=q^{m-1}\), giving a ratio tending to \(q/(q-1)\). Replacing each entry by a two-dimensional alternating block gives the same ratio for alternating spaces.

## 2. Positive quadratic factor tables

Let \(Q_i:V\to H_i=\mathbb F_q^{k_i}\) be explicitly specified maps of degree at most two, with complete positive rational tables \(w_i\) on \(H_i\). The requested mathematical quantity is the exact normalizing sum of
\[
                         W(x)=\prod_i w_i(Q_i(x)).
\]
Include in \(\mathcal S\) all the scalar polar forms of the coordinate quadratics:
\[
           B_Q(u,v)=Q(u+v)-Q(u)-Q(v)+Q(0).
\]
This is bilinear and symmetric in every characteristic, alternating in characteristic two. Write \(V=A\oplus U\) for any complement \(A\) of the space delivered by (1), and \(c=\dim A\). For each of the \(q^c\) choices \(a\in A\), the map \(u\mapsto Q_i(a+u)-Q_i(a)\) is additive on \(U\); its cross difference is \(B_{Q_i}(u,u')=0\). It is therefore linear over the prime field. This treatment does not silently discard squares in characteristic two; a square term on \(U\) is additive, though it need not be \(\mathbb F_q\)-linear for nonprime \(q\). The additive map can be constructed by evaluation on a prime-field basis of \(U\). Restrict its codomain to its image and reindex the table by the affine offset \(Q_i(a)\), yielding explicit positive group factors of the form treated in [the exact positive group weight theorem](https://github.com/mxym/math/blob/2cd1edf7447ba7f75b6f88f8fdd030e71da9e9c9/research/euclidean-tensor-geometry/theoretical-cryptography/positive-group-weight-factorization.md).

For each slice, use that theorem on the additive vector space over the prime field to find its intrinsic linear independent blocks. If every *nonconstant* block over all slices has cardinality at most \(B\), then \(W\) can be normalized exactly in \(q^c\,\mathrm{poly}(L,B)\) bit time, where \(L\) is the explicit input length. In fact one can sum each slice by its product-block identity, accounting for uniform directions by multiplying by their group cardinality, then sum over \(a\). A common denominator can be taken as the product of all denominators in the input factor tables; it bounds denominator growth for every true partial sum. No numerical approximations enter. For fixed \(q\), \(r=O(\log L)\) and \(B=\mathrm{poly}(L)\) make this polynomial. One can also use the actual \(c\), possibly much smaller than the bound, and decline to enumerate if it exceeds a chosen budget. The small-block condition is deterministically testable within the branch budget; it is separate from low polar rank.

To illustrate a dense-scope case, let \(V=\mathbb F_q\oplus\mathbb F_q^{N-1}\), with coordinates \((z,y)\), and let \(l_i\) form a basis of the dual of the \(y\)-space, not necessarily sparse in the input coordinates. Take \(Q_i(z,y)=z\,l_i(y)\). Every linear combination of polar matrices has rank at most two, while the joint radical can be zero. The procedure may choose any nonzero generator first, immediately yielding \(U=\{z=0,\ l_j(y)=0\}\) for some \(j\). All remaining slice maps are scalar functions of the independent restricted \(l_i\)'s. Hence all nonconstant blocks are one-dimensional over \(\mathbb F_q\) or split further over the prime field. This provides exact normalization even when scopes in the given coordinates are large.

Conversely low generic polar rank alone is not enough for the small-block route. With a prime-field base, add to the same example the form \(z\sum_i l_i(y)\), with a nonconstant positive table. On \(z\ne0\), if the first generator chosen is one of the basis forms, the intrinsic conditional Fourier lines now contain the surviving independent \(l_i|_U\) and their sum. If the first is the added sum, the restricted basis forms instead have the one full-support dependence \(\sum_i l_i|_U=0\), with the same conclusion. For \(N-2\ge2\) these span a single matroid component of dimension \(N-2\): choose rational nonconstant tables, and distinct dual lines contribute separate log frequencies, so there is no linear separation into smaller nonconstant blocks. This is a precise limitation of this criterion, not a claim that that particular normalizer cannot be evaluated by another algorithm.

## 3. Provenance and scope

The bordered-minor step uses the same classical rank extraction idea appearing in [de Seguins Pazzis, *Large spaces of symmetric or alternating matrices with bounded rank*, §2](https://arxiv.org/html/1603.08560#S2) and in [Gow, common isotropic points of constant-rank spaces](https://arxiv.org/abs/1502.05547). The finite-field specialization factor is credited above. [Bei–Chen–Guan–Qiao–Sun, §3.2](https://arxiv.org/abs/1904.03950) gives a different greedy construction of an inclusion-maximal isotropic subspace of an alternating matrix space, while also studying the harder maximum-dimension problem. The point here is an iteration with an exact total generic-rank budget, requiring no maximum finite-field or extension-field member, and a bit-complexity consequence for explicit, strictly positive quadratic factor normalizers with certified small affine-slice blocks. The normalizer conclusion genuinely uses the block hypothesis, and does not solve arbitrary systems of quadratics, noisy sample inversion, or a cryptographic target.
