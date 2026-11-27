# Proof

## Statement

Fix a prime power \(q\), and take \(1\le r\le k\). A labelled family
\((E_i)_{i\in[n]}\) of \(r\times k\) matrices is a weak lossless
\((k,r,L)\) rank extractor if for every rank-\(r\) matrix
\(M\in\mathbb F_q^{k\times r}\) at most \(L\) indices satisfy
\(\operatorname{rank}(E_iM)<r\). Equivalently, for every \(r\)-subspace
\(U\) of \(\mathbb F_q^k\), at most \(L\) restrictions \(E_i|_U\) have
a nonzero kernel. This is the indexed weak definition of
Guo–Raj–Shangguan–Zhang, arXiv:2604.13431v2, §1, with output
dimension exactly \(r\).

There are deterministic families with \(L=\lfloor7n/8\rfloor\) for
\(q=2\), and \(L=\lfloor25n/48\rfloor\) for \(q\ge3\). For each fixed
\(q\) their sizes are at most \(k2^{6r+o(r)}\) for \(q=2\) and at most
\(kq^{2r+o(r)}\) for \(q\ge3\), with \(o(r)\) as \(r\to\infty\)
independent of \(k\). The enumeration takes time polynomial in
\(k,q^r\) for each fixed \(q\).

## 1. Approximately uniform low-dimensional evaluations

Regard the input space as \(K=\mathbb F_{q^k}\) by an ordered
\(\mathbb F_q\)-basis; let \(\pi:K\to\mathbb F_q^r\) project to its
first \(r\) coordinates. For \(1\le m\le r\) and
\(a=(a_0,\dots,a_{m-1})\in K^m\), define
\[
 E_a(x)=\pi\biggl(\sum_{j=0}^{m-1}a_j x^{q^j}\biggr).
\]
The Frobenius powers are linear over \(\mathbb F_q\), so \(E_a\) is
\(\mathbb F_q\)-linear. Let \(W\le K\) have dimension \(s\le m\) and
basis \(x_1,\ldots,x_s\). The \(s\times s\) matrix whose \((i,j)\)-entry
is \(x_i^{q^{j-1}}\) is nonsingular over \(K\): a nontrivial column
dependence would give a nonzero linearized polynomial of ordinary
degree at most \(q^{s-1}\) vanishing on the \(q^s\) distinct elements
of \(W\), which is impossible. The first \(s\) coefficients already
make evaluations surjective onto \(K^s\); applying \(\pi\) coordinate
by coordinate preserves surjectivity onto \((\mathbb F_q^r)^s\).
Thus uniform coefficients kill \(W\) with probability \(q^{-rs}\).

Use an indexed \(\varepsilon\)-biased coefficient multiset in the
additive group \(K^m\): every nontrivial additive character has mean
of magnitude at most \(\varepsilon\). For a surjective linear map
\(T\) to a finite additive group \(G\), the character identity
\(1_{\{T(a)=0\}}=|G|^{-1}\sum_{\chi\in\widehat G}\chi(T(a))\)
holds. A nontrivial character remains nontrivial after pullback by
\(T\). Take \(T(a)=(E_a(x_1),\ldots,E_a(x_s))\) to obtain
\[
 \left|\Pr_i[E_{a_i}|_W=0]-q^{-rs}\right|
 \le (1-q^{-rs})\varepsilon\le\varepsilon.                 \tag{1}
\]
This needs no statistical independence of the sampled coefficients;
the argument also applies to non-prime fields using additive
characters.

## 2. Fields with \(q\ge3\)

Take \(m=1\) and \(\varepsilon=(24q^r)^{-1}\). Failure on an
\(r\)-subspace \(U\) means killing at least one of its
\((q^r-1)/(q-1)\) projective lines. The union bound and (1) give
\[
 \Pr[\text{failure}]
 \le\frac{q^r-1}{q-1}(q^{-r}+\varepsilon)
 <\frac{25}{24(q-1)}\le\frac{25}{48}.
\]
This includes \(r=1\) and \(r=2\).

## 3. Binary field

Take \(m=\min(3,r)\), \(v=2^r\), and
\(\varepsilon=(24v^3)^{-1}\). For each of the \(v-1\) nonzero points
\(x\in U\) let \(A_x\) be the event \(E_a(x)=0\). Write \(S_j\)
for the sum of the probabilities of intersections of \(j\) distinct
events, counted unordered. The third Bonferroni lower bound is
\[
 \Pr[\text{success}]\ge1-S_1+S_2-S_3.                    \tag{2}
\]
At an outcome lying in \(z\ge1\) of the events, the right-hand
indicator polynomial is \(1-z+\binom z2-\binom z3=-\binom{z-1}3\le0\);
at \(z=0\) it is 1.

Each pair of distinct nonzero points spans a plane. Each distinct
triple spans a plane or a 3-space; the planar case is exactly
\(\{x,y,x+y\}\). Every ordered distinct pair determines one such
triple and each dependent triple is counted by six ordered pairs.
Consequently the dependent and independent triple counts are
\[
 D=\frac{(v-1)(v-2)}6,\qquad
 I=\binom{v-1}3-D=\frac{(v-1)(v-2)(v-4)}6.
\]
For \(r=1\) and \(r=2\), \(I=0\); the \(r=1\) case also has no
pairs or dependent triples. Thus (1) never needs a dimension
larger than \(m\). With uniform coefficients, the right side of
(2) is exactly
\[
\begin{aligned}
 B(v)&=1-\frac{v-1}{v}+\frac{(v-1)(v-2)}{2v^2}
             -\frac D{v^2}-\frac I{v^3}\\
 &=\frac1v+\frac{(v-1)(v-2)(v+4)}{6v^3}
   =\frac16+\frac{7v^2-10v+8}{6v^3}\ge\frac16.
\end{aligned}
\]
The last numerator is positive for \(v\ge2\). In the two boundary
cases \(B(2)=1/2\) and \(B(4)=3/8\); these are also their exact
uniform-coefficient success probabilities.

By (1) the total absolute change in the three sums is at most
\[
 \varepsilon\left[(v-1)+\binom{v-1}2+\binom{v-1}3\right]
 =\varepsilon\frac{(v-1)((v-1)^2+5)}6
 <\frac{\varepsilon v^3}6=\frac1{144},
\]
since \(v^3-(v-1)((v-1)^2+5)=3v^2-8v+6>0\).
Applying (2) yields success greater than \(23/144\), in particular
at least \(1/8\).

## 4. Enumeration and scopes

Construct the polynomial basis of \(K\) by a deterministic
irreducible-polynomial algorithm over \(\mathbb F_q\) (Shoup, fixed
characteristic). Apply Jalan–Moshkovitz, Theorem 1.1 and §3.4, to
\((\mathbb F_q,+)^{mk}\) in that basis; the family of generators,
sampled by index, has the desired character bias and size
\(O_q(mk\,\varepsilon^{-(2+o(1))})\), with enumeration time polynomial
in \(mk,1/\varepsilon\) for fixed \(q\). The binary small-bias
construction of Ta-Shma can also be used. Group each sample into
\(m\) elements of \(K\) and evaluate \(E_a\) on the \(k\) basis
vectors to construct its \(r\times k\) matrix. If needed to guarantee
output-sensitive time, repeat the entire index list uniformly until
\(n\ge1/\varepsilon\), adding fewer than \(\lceil1/\varepsilon\rceil\)
labels to its initial length bound and leaving proportions unchanged.
This gives time polynomial in \(k,n\) for fixed \(q\), as in the
explicitness convention of §1 footnote 1.

Substitute the chosen biases and use \(m\le3\) for the size bounds.
In particular the index length satisfies
\(\log_2 n\le\log_2 k+(6+o(1))r\) for \(q=2\) and
\(\log_2 n\le\log_2 k+(2+o(1))r\log_2q\) for fixed \(q\ge3\).
The uniform seed space is \([n]\), not assumed to be a power of two.

A list may include repeats, either in the coefficient sample or after
mapping to matrices. No claim is made that deduplicating preserves the
success fraction. In contrast, removing globally rank-deficient
matrices preserves it: at least the stated fraction has full global
rank by testing any fixed \(r\)-subspace, and removed indices are bad
on every \(r\)-subspace, so each good numerator is unchanged and the
denominator only decreases. The resulting length is still at least a
constant fraction of the unfiltered length.

This proves the constant success threshold of §7 item 5 with the
stated size \(kq^{O(r)}\), and improves the rank dependence of the
stated fixed-\(q\) multilinearity field-reduction construction when
\(k\) is much larger than \(r\). For \(r=O(\log k)\) with \(q\) fixed,
both the size and enumeration are polynomial in \(k\). For arbitrary
\(r\) this is not a claim of polynomial size in \(k,r\), strongly
explicit evaluation, or a strong lossless rank extractor.
