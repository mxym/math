# The actual smoothing cutoff for a three-factor cyclotomic tensor

Let \(A_{n-1}=\{x\in\mathbb Z^n:\sum_j x_j=0\}\), and let
\[
 F=A_{n_1-1}\otimes A_{n_2-1}\otimes A_{n_3-1},\qquad \Lambda=F^*,
 \qquad \Theta(a)=\sum_{X\in F} a^{\|X\|^2},\quad 0<a<1 .
\]
Here \(F\) is equivalently the space of integer arrays with zero sum on every coordinate line, and the squared norm is the sum of squared entries. Suppose \(n_i/N\to\beta_i\in(0,\infty)\). Write \(I(r)=\sup_{t\ge0}(tr-\log I_0(t))\) for the circle mean rate function, as in the [fixed macroscopic companion](https://github.com/mxym/math/blob/9e241e4d3f5a629ea956cc9b64eb83df50fa58cd/research/euclidean-tensor-geometry/theoretical-cryptography/triple-cyclotomic-macroscopic.md). Define
\[
 c_*(\boldsymbol\beta)=
 \inf_{\substack{0<r_1,r_2,r_3<1}}
 \frac{\beta_1\beta_2 I(r_1)+\beta_2\beta_3 I(r_2)+\beta_3\beta_1 I(r_3)}
                 {2\beta_1\beta_2\beta_3 r_1r_2r_3}.
 \tag{1}
\]
It is positive and finite: \(I_0(t)\le e^{t^2/4}\) by its power series gives \(I(r)\ge r^2\), so apply AM–GM to the numerator; finiteness follows by taking \(r_i=1/2\). In the balanced case this is the companion's \(c_*=2.380887\ldots\). The companion proves \(N^{-2}\log\Theta(c/N)\to0\) for \(c<c_*(\boldsymbol\beta)\) and a strictly positive limit for \(c>c_*(\boldsymbol\beta)\). The first of these alone does not imply \(\Theta(c/N)\to1\).

**Theorem.** For every fixed \(0<c_0<c_*(\boldsymbol\beta)\), uniformly over \(0<a\le c_0/N\) as \(N\to\infty\),
\[
 \begin{split}
 \Theta(a)&=1+B_8 a^8+B_{12}a^{12}+P_{16}a^{16}+O(N^{-5}),\\
 \log\Theta(a)&=B_8 a^8+B_{12}a^{12}+O(N^{-5}),\\
 B_8&=2\prod_{i=1}^3\binom{n_i}{2},\\
 B_{12}&=12\sum_{i=1}^3\binom{n_i}{2}\prod_{j\ne i}\binom{n_j}{3},\\
 P_{16}&=2\prod_{i=1}^3\binom{n_i}{2}\binom{n_i-2}{2}.
 \end{split}                                                        \tag{2}
\]
In particular at fixed \(c\in(0,c_*(\boldsymbol\beta))\), \(\Theta(c/N)-1\sim(\beta_1\beta_2\beta_3)^2 c^8/(4N^2)\). The \(N^{-4}\) terms in (2) come from two opposite length-six layer cycles and from pairs of cubes disjoint in each coordinate. The disconnected cube pairs cancel in the logarithm to the displayed accuracy. No assertion is made about the unnormalized mass at \(c=c_*(\boldsymbol\beta)\), or in a shrinking window around it.

Consequently for every fixed \(\epsilon>0\), the Euclidean smoothing width of \(\Lambda\) satisfies
\[
               \pi\,\eta_\epsilon(\Lambda)^2-\log N
                      \longrightarrow -\log c_*(\boldsymbol\beta).
 \tag{3}
\]
By the canonical isometry in the companion note, when the \(n_i\) are distinct odd primes \(p_i\), the integer-ring lattice of conductor \(p_1p_2p_3\) is \(\sqrt{p_1p_2p_3}\,\Lambda\) up to isometry; use those rescaled widths in (3). This is a fixed-\(\epsilon\) theorem, not an estimate for exponentially small \(\epsilon\), a wrapped-noise TV profile, or a claim about a cryptosystem.

## 1. Pairing arbitrary signed multiplicities

For \(X\in F\), let \(m=\sum_{X_{ijk}>0} X_{ijk}=\frac12\|X\|_1\). Think of its positive and negative parts as multisets of \(m\) triples each. They have disjoint supports. The zero line sums say that, between the two multisets, each of the three pair-coordinate marginals agrees. On any ordered positive and negative lists there is at least one matching bijection for each of these three pairs of coordinates.

The number of ordered lists for a given \(X\) is \((m!)^2/\prod_{ijk}|X_{ijk}|!\). Moreover for \(a\le1/2\),
\[
             a^{\|X\|^2}\le
                     \frac{a^{2m}}{\prod_{ijk}|X_{ijk}|!}.
 \tag{4}
\]
Indeed \(a^{j(j-1)}\le1/j!\) for each integer \(j\ge0\), using \(j!\le2^{j(j-1)/2}\) for \(j\ge1\). Thus the total mass at \(m\) is at most \(a^{2m}/(m!)^2\) times the number of ordered sign lists with three recorded pair-match bijections. This handles repeated triples without assuming that the arrays are partial Latin squares or merely \(\{-1,0,1\}\)-valued.

Let \(\sigma,\tau,\pi\) match the positive label \(\ell\) to the negative label at equal coordinates \((i,j),(j,k),(k,i)\), respectively. Relabel the negative list to make \(\pi\) the identity; there are \(m!\) original \(\pi\) choices. If the positive labels are \(p_\ell=(i_\ell,j_\ell,k_\ell)\), the first coordinates of positive and negative label \(\ell\) agree, as do the third coordinates. It follows that \(i_\ell\) is constant on cycles of \(\sigma\), \(k_\ell\) on cycles of \(\tau\), and \(j_\ell\) on cycles of \(\tau^{-1}\sigma\). Conversely these conditions are exactly sufficient to assign all coordinates subject to the recorded match constraints (the second coordinate of negative label \(\sigma(\ell)\) is \(j_\ell\)). If \(\sigma\) or \(\tau\) fixes some label, or if \(\tau^{-1}\sigma\) fixes some label, one positive and one negative triple share two of the three coordinate pairs, hence all coordinates. This is forbidden by disjoint signs. We may relax disjointness after retaining those three derangement restrictions.

Writing \(c(\nu)\) for the number of cycles, put \(f_i(\nu)=n_i^{c(\nu)}\mathbf1_{\{\nu\text{ has no fixed point}\}}\) on the symmetric group. The weighted representation count yields
\[
 \sum_{X:m(X)=m}a^{\|X\|^2}
 \le\frac{a^{2m}}{m!}
     \sum_{\sigma,\tau} f_1(\sigma)f_2(\tau^{-1}\sigma)f_3(\tau)
 \le\frac{a^{2m}}{m!}\prod_{i=1}^3\|f_i\|_{3/2}.
 \tag{5}
\]
For the last step use Young's convolution inequality with counting measure, \(\|f_3*f_2\|_3\le\|f_3\|_{3/2}\|f_2\|_{3/2}\), then Hölder. Directly, for nonnegative \(F,G\), apply Hölder with three exponents 3 to the factors \(F(y)^{1/2}G(y^{-1}x)^{1/2}\), \(F(y)^{1/2}\), \(G(y^{-1}x)^{1/2}\) in the convolution; cube and sum over \(x\). The cycle-weighted derangement sum is
\[
   \sum_{\nu:\mathrm{no\ fixed\ point}}T^{c(\nu)}
      =m!\,[z^m]\exp(T H(z)),\qquad
           H(z)=\sum_{\ell\ge2}\frac{z^\ell}{\ell}.
\]
This follows by grouping permutations with \(h_\ell\) cycles of length \(\ell\), counted by \(m!/\prod_\ell \ell^{h_\ell}h_\ell!\). Taking \(T=\max_i n_i^{3/2}\), (5) gives the key common bound
\[
       \sum_{X:m(X)=m}a^{\|X\|^2}\le
                     a^{2m}m!\,\big([z^m]\exp(T H(z))\big)^2 .
 \tag{6}
\]
The cycle encoding has a standard antecedent for Latin bitrades in the work of Drápal and in [Cavenagh–Drápal–Hämäläinen](https://arxiv.org/abs/0704.1730); see also [Gessel's cycle-weighted count of triples of relative derangements](https://people.brandeis.edu/~gessel/homepage/papers/3latin.pdf). Here (4)–(6) keep all signed integer multiplicities and use a norm bound rather than a bitrade classification.

## 2. From bounded energy to the macroscopic window

In this section take \(a=c_0/N\); \(T=\Theta(N^{3/2})\) as a size estimate (not the theta function). For \(1\le m\le T/4\), use coefficient positivity at \(z=\sqrt{m/T}\le1/2\), where \(H(z)\le z^2\). This gives
\[
       [z^m]e^{TH(z)}\le e^m (T/m)^{m/2},\qquad
       \sum_{X:m(X)=m}a^{\|X\|^2}\le(e^2 a^2T)^m.
 \tag{7}
\]
Here \(m!\le m^m\). The base \(e^2a^2T=O(N^{-1/2})\), so the total with \(10\le m\le T/4\) is \(O(N^{-5})\).

When \(m>T/4\), evaluate the generating series at \(z=1/2\), giving coefficient at most \(2^m e^{TH(1/2)}\). Since \(T<4m\), the bound in (6) is \((C a^2 m)^m\) for the absolute constant \(C=4e^{8H(1/2)}\). Choose fixed \(\delta>0\) so \(C c_0^2\delta<1/2\). Summing \(T/4<m\le\delta N^2\) gives \(O(2^{-T/4})\).

For \(m>\delta N^2\), pick fixed \(c_1\in(c_0,c_*(\boldsymbol\beta))\), and set \(a_1=c_1/N\). Since \(\|X\|^2\ge2m\), the rest is bounded by
\[
            (a/a_1)^{2\delta N^2}\,\Theta(a_1).
\]
The macroscopic companion, Theorem (1), says \(\log\Theta(a_1)=o(N^2)\). Hence the displayed bound is exponentially small on scale \(N^2\). This is the only macroscopic input: the permutation estimate bridges from finite \(m\) to a fixed fraction of \(N^2\), at which the strictly subcritical larger parameter pays for the rest. All summands are nonnegative and monotone in \(a\), so the \(O(N^{-5})\) tail for \(m\ge10\) also holds uniformly for \(0<a\le c_0/N\).

## 3. Classifying the leading small configurations

For each nonzero array, consider the two-dimensional slices along any of its coordinates. At least two slices are nonzero, by the line sums along that coordinate. Each nonzero slice is a matrix with zero row and column sums. Directing the positive multiedges from rows to columns and negative ones in the reverse direction creates a balanced directed bipartite multigraph. It decomposes, without cancellation, into directed simple cycles by repeatedly removing a cycle. There is no 2-cycle because each cell has a single sign. Thus the slice has \(\ell^1\) mass at least 4, and for mass 4 or 6 it is a single alternating cycle of that length with unit entries. The number of distinct used labels along any coordinate is therefore at most \(\lfloor m/2\rfloor\). With \(m\) fixed and total \(k\) used labels, the number of arrays is \(O_m(N^k)\): there are finitely many patterns after choosing the labels, since every entry has bounded magnitude and each used dimension is bounded by \(m\).

For \(m<4\) no nonzero array is possible. If \(m=4\), there are two opposite slices in every coordinate, each a unit-signed rectangle. Thus the array is the alternating cube on a pair of labels in each coordinate, giving \(B_8\). The case \(m=5\) is impossible: it would have two slices in each coordinate. Any two opposite slices have equal and even \(\ell^1\) masses, making the full mass divisible by four, whereas \(2m=10\).

For \(m=6\), any axis with two slices has two opposite unit-signed length-six cycles, using three labels in each other dimension. Per \(3\times3\) choice there are six unoriented Hamilton cycles of the bipartite graph \(K_{3,3}\), since \((3!)^2/(2\cdot3)=6\); each has two choices of sign. The two-slice axis is unique in this case, giving exactly \(B_{12}\). It remains to exclude three used labels in every dimension. Then every two-dimensional slice has mass 4 and is a rectangle with unit entries. In the bipartite graph of used pairs of first and second labels, each vertex has degree 2: fixing a first label shows exactly two second labels in its rectangle slice, and the same holds reversing roles. So this graph is a simple 2-regular graph on \(3+3\) vertices, necessarily a single length-six cycle. But each third-coordinate rectangle requires a length-four cycle in that graph, a contradiction. These cube and length-six shapes are familiar as elementary moves for fixed two-dimensional marginals; compare [Diaconis–Sturmfels, §4](https://doi.org/10.1214/aos/1030563990) and [Aoki–Takemura on \(3\times3\times K\) tables](https://doi.org/10.1111/1467-842X.00278). The argument here counts the actual signed lattice vectors, not just generators of a Markov basis.

For \(m=7\), there are at most nine used labels, so the contribution is \(O(N^9 a^{14})=O(N^{-5})\). For \(m=8\), patterns with at most eleven used labels likewise contribute \(O(N^{11}a^{16})=O(N^{-5})\). If there are twelve used labels, all three dimensions use four labels and all slices are unit rectangles. The used bipartite pair graph for the first and second indices is simple 2-regular on \(4+4\) vertices as before. It must contain a rectangle, from any third-coordinate slice, so it is two disjoint length-four cycles, not one length-eight cycle. Every third-coordinate slice uses exactly one of the two blocks. Every used pair from one block appears in exactly two slices: fixing its first label gives a rectangle using two second and two third labels. Thus two opposite third-coordinate slices occupy each block. This describes exactly two cubes disjoint in each coordinate. The two signs and the unordered pair of disjoint pair choices in the three coordinates give \(P_{16}\): first order the two cubes, choose pairs successively and multiply by four signs, then divide by two.

For \(m=9\), there are at most twelve used labels, so the contribution is \(O(N^{12}a^{18})=O(N^{-6})\).

These cases and the tail in §2 prove the first line of (2). For the logarithm, \(B_8a^8=O(N^{-2})\), while each newly retained correction is \(O(N^{-4})\). In the squared term of the Taylor expansion for \(\log(1+x)\) only \((B_8a^8)^2/2\) matters at this accuracy. Since \(P_{16}=(1+O(N^{-1}))B_8^2/2\), it cancels \(P_{16}a^{16}\) up to \(O(N^{-5})\). Cubic and mixed higher terms are \(O(N^{-6})\).

## 4. True smoothing, rather than normalized free energy

In these units, \(\eta_\epsilon(\Lambda)\) is the least \(s>0\) such that \(\Theta(e^{-\pi s^2})\le1+\epsilon\). Fix arbitrary \(0<c_-<c_*(\boldsymbol\beta)<c_+\). Equations (2) and the macroscopic companion give respectively \(\Theta(c_-/N)\to1\) and \(\Theta(c_+/N)\to\infty\) (the latter has a positive order-\(N^2\) logarithm). Monotonicity sandwiches the smoothing offset between \(-\log c_+\) and \(-\log c_-\) for large \(N\); bring \(c_\pm\) to \(c_*(\boldsymbol\beta)\) to prove (3).

[Lyubashevsky–Peikert–Regev, Definition 2.1 and Lemma 2.3](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf) use the Gaussian smoothing condition for abstract residue comparison, and [Micciancio–Peikert, Corollary 2.7](https://web.eecs.umich.edu/~cpeikert/pubs/LWsE.pdf) gives a general tensor smoothing bound. The finite-coset factorization in [Liu–Liang–Ding, ePrint 2026/2028](https://opencryptology.org/2026/2028) is a different, exact theta evaluation identity and leaves the outer residue sum. None of these supplies the subcritical unnormalized mass control above. This note concerns only the fixed-ratio three-factor family, with no higher-factor extrapolation and no efficiency, attack, or hardness implication.

The companion checker verifies the cycle inventories, Young bound, normalization with signed multiplicities, and small shell counts exactly. The asymptotic upper bound follows from the analytical tail argument, not finite enumeration.
