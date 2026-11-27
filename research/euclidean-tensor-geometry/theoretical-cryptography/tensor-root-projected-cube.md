# When the projected cube ceases to be a Voronoi cell of a tensor-root lattice

Let \(n_i\ge2\), let \(A_{n_i-1}\) be the integer zero-sum lattice in \(\mathbb R^{n_i}\) with its ordinary Euclidean metric, and put
\[
 L=\bigotimes_{i=1}^k A_{n_i-1},\quad W=\operatorname{span}_{\mathbb R}L,\quad
 N=\prod_i n_i,\quad d=\prod_i(n_i-1).
\]
View \(W\) in the Euclidean array space \(\mathbb R^N\), and let \(P\) be its orthogonal projector. The goal is to compare the actual Voronoi cell \(V(L)\) with the specific projected cube \(Z=P[-1/2,1/2]^N\), not with arbitrary zonotopes or arbitrary embeddings.

* The cube projection is always contained in the Voronoi cell. It equals it **if and only if at most two of the \(n_i\) exceed 2**. For three nontrivial factors, a single explicit primitive circuit gives a positive Euclidean gap, even if all their sizes are increased.
* The circumradius of the projected cube is exactly \(\sqrt{N}/2\) if all the sizes are even; otherwise it is \(\tfrac12\sqrt{N(1-p^{-2})}\) for the smallest odd size \(p\). This is the actual covering radius when there are at most two nontrivial factors and a certified lower bound otherwise.
* In the strict regime the error need not be small. A determinant bound shows the cube projection occupies an exponentially vanishing fraction of the true Voronoi cell for three or more growing sizes, quantitatively when the reciprocal-size entropy exceeds one nat. This includes equal sizes and sufficiently close comparable distinct primes. A second bound applies along growing lists of distinct primes.
* These statements apply to a specified principal ideal with its canonical trace metric in an odd squarefree cyclotomic field; the similarity factor is exactly \(\sqrt m\) for conductor \(m\) in the trace convention below.

No closest-vector procedure, cryptographic instance, or security claim is involved.

## 1. Geometry and the exact equality criterion

An array is in \(W\) exactly when every line sum in each coordinate direction is zero, and \(L=W\cap\mathbb Z^N\). In fact, assign free values on the core \(0\le j_i\le n_i-2\) and extend by making the last entry on every line minus the sum of earlier entries. Equivalently one uses the integral basis obtained by tensoring \(e_j-e_{n_i-1}\). If \(Q_i\) averages along the \(i\)-th coordinate, keeping its dimension, then these orthogonal projections commute and \(P=\prod_i(I-Q_i)\).

For \(w\in W\), the support function of \(Z\) is \(\|w\|_1/2\). For integral \(w\) it is at most \(\|w\|^2/2\), so all Voronoi inequalities hold on \(Z\). In the one- or two-factor case the zero-sum space is a real graph flow space: respectively the two-vertex parallel-edge graph, or the complete bipartite graph with an edge for each array entry. Every real flow decomposes conformally into simple directed cycles with nonnegative real coefficients: orient each nonzero edge in the flow's sign, follow nonzero edges until a cycle appears, subtract the smallest remaining weight on its edges, and repeat. The cycles have entries \(0,\pm1\); therefore their Voronoi inequalities imply \(\langle w,x\rangle\le\|w\|_1/2\) for every real \(w\in W\) on the whole \(V(L)\). This is exactly the support-function description of \(Z\). If some \(n_i=2\), factor off \(e_0-e_1\): the resulting array lattice and projected cube both acquire the same similarity factor \(\sqrt2\). Indeed the reduction of the cube uses the difference of two slices divided by two, which ranges over the same cube in the remaining coordinates. If there were no remaining factors, this is the one-dimensional integer interval case. This proves equality for at most two sizes above two.

For strictness in the three-factor case, first take \(3\times3\times3\), using indices \(0,1,2\) and the core \(0,1\) in every direction. Put
\[
 w_{000}=-2,\qquad w_{100}=w_{010}=w_{001}=1,\qquad
 w_{011}=w_{101}=w_{110}=w_{111}=0
\]
and extend via zero line sums. This integral vector is primitive. Its support carries only the one-dimensional real subspace \(\mathbb Rw\). To see this, any array supported there has only four free core entries, say \(D,A,B,C\) at \(000,100,010,001\). The zero entries at \(022,202,220\) require \(D+B+C=D+A+C=D+A+B=0\), forcing \(A=B=C,\ D=-2A\). In larger dimensions pad with zeros along the first three axes and tensor the witness along every extra axis with \(e_0-e_1\). An array supported in this enlarged support must factor along those extra axes by zero line sums, so the real support subspace is still one-dimensional. The resulting primitive witness still has an entry of magnitude two.

Here is a quantitative way to see why this circuit matters. Let \(s=\operatorname{sign}(w)\) entrywise with zero for absent entries, and \(S=\#\operatorname{supp}(w)\). The point \(x_0=Ps/2\) is in \(Z\) and saturates its supporting inequality in direction \(w\). For any nonzero \(v\in L\), set \(D_v=\|v\|^2-\langle s,v\rangle\). If \(D_v=0\), the integer vector \(v\) is supported within the support of \(w\), sign-conformal and has entries at most one in magnitude. It would have to be a nonzero integer multiple of \(w\), contradiction. Thus \(D_v\ge1\). The entries with magnitude at least two contribute at least half their squared norm to \(D_v\); entries of magnitude one outside \(\operatorname{supp}(w)\) contribute at least half, and at most \(S\) other unit entries remain. Hence \(\|v\|^2\le2D_v+S\), so \(D_v/\|v\|\ge1/\sqrt{S+2}\). The closed \(W\)-ball of radius \(1/(2\sqrt{S+2})\) about \(x_0\) lies in \(V(L)\). Moving by this radius in the direction \(w/\|w\|\) leaves the supporting half-space of \(Z\) by exactly that distance. This establishes the strict inclusion and the Hausdorff lower bound. It is a statement about the natural array projection, not a classification of abstract zonotopal lattices.

## 2. An exact circumradius formula

A convex quadratic function on a cube attains its maximum at a sign vector, so \(4\operatorname{rad}(Z)^2=\max_{s\in\{\pm1\}^N}\|Ps\|^2\). If all sizes are even, a product of balanced sign vectors lies in \(W\), attaining \(N\). If \(n_a=p\) is the smallest odd size, each \(a\)-line has odd integer sum and therefore \(\|Q_a s\|^2\ge N/p^2\). Since \(P\) projects into \(\ker Q_a\), \(\|Ps\|^2\le N(1-p^{-2})\).

This bound is attainable simultaneously across the other axes. Relabel the smallest odd axis as \(a\). On it, use the residues \(0,\ldots,p-1\) with no sign multiplier. For every other odd axis, place one copy of each of those residues with multiplier \(+1\), then pair each of its remaining \(n_i-p\) positions using equal residues (say 0) and opposite multipliers. For an even axis use residue 0 at all its positions and equal numbers of each multiplier. Choose \(f:\mathbb Z/p\mathbb Z\to\{\pm1\}\) with sum 1. Define the array by
\[
 s_{j_1,\ldots,j_k}=
 \left(\prod_i \varepsilon_i(j_i)\right)
 f\!\left(\sum_i b_i(j_i)\bmod p\right),
\]
where \(b_i\) and \(\varepsilon_i\) are the indicated residue and multiplier. The \(a\)-line sums each have absolute value one. Summing over any other odd axis gives the product of the other multipliers, independent of \(j_a\), since the extra pairs cancel and the first \(p\) residues exhaust \(f\). Summing over an even axis gives zero. Thus \(Q_i s=Q_aQ_i s\) for \(i\ne a\). As the \(Q_i\) commute, \(P s=(I-Q_a)s\); its squared norm is \(N(1-p^{-2})\). This proves the formula, with no growth or parity restriction on the other axes.

## 3. Quantitative volume loss

Let \(B\) be the \(N\times d\) matrix of the integral basis above. For a \(d\)-element row subset \(I\) set \(D_I=|\det B_I|\). In orthonormal coordinates of \(W\), the generator of the cube projection from ambient coordinate \(j\) is the \(j\)-th row of \(B(B^TB)^{-1/2}\). The volume formula for a zonotope sums the absolute determinants of all independent generator choices, and Cauchy–Binet gives the sum of squared minors. Dividing by the lattice covolume \(\sqrt{\det(B^TB)}\) gives
\[
 F=\frac{\operatorname{vol}_d Z}{\operatorname{vol}_d V(L)}
   =\frac{\sum_I D_I}{\sum_I D_I^2}
   \le \min\left\{1,\sqrt{\frac{\binom{N}{d}}{\prod_i n_i^{\,d/(n_i-1)}}}\right\}.
 \tag{1}
\]
Here the Gram determinant follows from tensoring \(I+J\) in each dimension \(n_i-1\); the inequality uses integrality and Cauchy–Schwarz. Formula (1) is an equality-free upper bound; it does not turn the exact circumradius of \(Z\) into an upper bound on the true covering radius.

Two consequences are useful even when individual minors are unavailable. First, let \(k\) be fixed, \(x_i=1/n_i,\ S_1=\sum x_i\to0\), and \(a_i=x_i/S_1\). With \(H(a)=-\sum a_i\log a_i\), all logarithms natural,
\[
 \log F\ \le\ \frac{NS_1}{2}(1-H(a))
             +O_k\!\left(NS_1^2\log(1/S_1)\right).
 \tag{2}
\]
Indeed \(N-d=N(S_1+O_k(S_1^2))\) and \(\log\binom{N}{d}\le(N-d)(1+\log(N/(N-d)))\). The log determinant is
\[
 \sum_i \frac{d}{n_i-1}\log n_i =
 NS_1\big[\log(1/S_1)+H(a)\big]
    +O_k(NS_1^2\log(1/S_1)),
\]
using \(\sum_i x_i\log(1/x_i)=S_1[\log(1/S_1)+H(a)]\) and \(d/(n_i-1)=Nx_i(1+O_k(S_1))\). This proves (2). For sizes all \(n\) and fixed \(k\ge3\) it gives
\[
 \log F\le -\frac{k}{2}(\log k-1)n^{k-1}
                   +O_k(n^{k-2}\log n).
\]
In particular the loss persists for three axes and is not a high-order-only effect. Comparable sizes alone are not sufficient for this particular estimate; the explicit sufficient margin is \(H(a)>1\) bounded away from one, which holds when \(k\ge3\) and ratios are sufficiently close to one.

Second, without fixing \(k\), using \(\binom Nd\le(eN/d)^d\) in (1) gives
\[
 \log F\le
 \frac d2\left[1-\sum_i\left(\frac{\log n_i}{n_i-1}
                              -\log\frac{n_i}{n_i-1}\right)\right].
 \tag{3}
\]
For a growing initial list of odd primes the summand is at least \((\log n_i-1)/(n_i-1)\), and the sum diverges by the classical divergence of reciprocal primes. Consequently for such a list \(F\le e^{-M d}\) eventually for every fixed \(M>0\).

## 4. A canonical ideal realizing these tensors

For an odd squarefree conductor \(m=\prod_i p_i\), work in \(K=\mathbb Q(\zeta_m)\) with inner product \(\langle a,b\rangle=\operatorname{Tr}_{K/\mathbb Q}(a\overline b)\); equivalently take the usual real canonical embedding with the \(\sqrt2\) factor on each complex pair. Inside \(K\), fix primitive \(p_i\)-th roots \(\zeta_{p_i}\) and consider the single ideal
\[
 \mathfrak a_m=\left(\prod_{p\mid m}(1-\zeta_p)\right)\mathcal O_K .
\]
For each prime \(p\), the trace Gram matrix on \(1,\zeta_p,\ldots,\zeta_p^{p-1}\) has diagonal \(p-1\) and off-diagonal \(-1\). Thus \(\zeta_p^j\mapsto \sqrt p(e_j-\mathbf1/p)\) is the isometry from its canonical realification to the zero-sum space, and multiplying by \(1-\zeta_p\) sends these elements to \(\sqrt p(e_j-e_{j+1})\) with cyclic indices. Those differences generate \(\sqrt p A_{p-1}\). Under multiplication, the tensor of the prime cyclotomic integer rings maps onto \(\mathcal O_K=\mathbb Z[\zeta_m]\) because the coprime prime roots generate \(\zeta_m\) and vice versa. The ranks agree, giving an integral identification. On all embeddings, choices for the respective prime fields are independent, so the trace Gram form multiplies. Therefore \(\mathfrak a_m\) is isometric to \(\sqrt m\,\bigotimes_{p\mid m} A_{p-1}\).

In particular, for one or two primes, with \(p_{\min}=\min_{p\mid m}p\), the squared covering radius of this **specific ideal** is \(m^2(1-p_{\min}^{-2})/4\). For three or more primes this expression is a lower bound; the canonical array cube projection is strictly smaller than the actual Voronoi cell, and its volume fraction obeys (1)–(3). The radius itself in that regime is not determined here.

## Prior work and exact audit

The one- and two-factor side is the classical integral-flow situation; see [Bacher–de la Harpe–Nagnibeda](https://www.numdam.org/item/10.24033/bsmf.2303.pdf), [Amini](https://arxiv.org/abs/1007.2456), and [Dancso–Lim](https://arxiv.org/abs/2202.13265) for the stronger graphic and regular-matroid Voronoi structure. Zero two-marginal constraints also appear in the distinct context of the no-three-factor-interaction model, e.g. [Takemura–Aoki](https://www.keisu.t.u-tokyo.ac.jp/data/2004/METR04-15.pdf). This note makes no claim that cube projection or non-unimodular three-way moves are new in isolation. The contributions are the natural-embedding equality criterion for all tensor sizes, its explicit Euclidean witness, the parity-sharp circumradius for any order, and the determinant-based asymptotic failure for the canonical ideal family.

The accompanying exact audit checks all 2,220,075 maximal minors of the fixed \(27\times8\) basis. Their absolute values are zero in 1,691,874 cases, one in 527,121, and two in 1,080. Therefore for \(A_2^{\otimes3}\) the exact volume fraction is \(529281/531441=19603/19683\). It also checks the small circuit and the parity construction in multiple tensor formats, including exhaustive sign vectors in six small formats. The small example is an abstract tensor, not a conductor with three copies of the same prime. No numerical observations are needed in the proofs.
