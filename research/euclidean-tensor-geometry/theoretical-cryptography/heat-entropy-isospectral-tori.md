# Heat-kernel entropy distinguishes Milnor's isospectral tori

Let \(T=\mathbb R^n/\Lambda\) be a flat torus, with Haar probability. Let \(p_t\) be its heat kernel from zero, written as a density with respect to that probability. Define
\[
R_\alpha(T,t)=\frac{1}{\alpha-1}\log\int_T p_t^\alpha,\qquad
R_1(T,t)=\int_Tp_t\log p_t ,
\]
for fixed finite \(\alpha>0\) (use continuity at 1), and \(R_\infty=\log\|p_t\|_\infty\).

**Theorem.** Let \(T_E=\mathbb R^{16}/(E_8\oplus E_8)\) and \(T_D=\mathbb R^{16}/D_{16}^+\) be Milnor's pair, and \(q=e^{-4\pi^2t}\). Then
\[
R_\alpha(T_D,t)-R_\alpha(T_E,t)
=86016\,\alpha(\alpha-2)(\alpha-3)(\alpha-4)\,q^{10}+O_\alpha(q^{12}).
\]
The formula includes \(\alpha=1\), with leading coefficient \(-516096\). Consequently each fixed finite positive Rényi order other than \(2,3,4\) distinguishes the pair for all sufficiently large times and for all positive times outside a discrete set. The three exceptional orders, and order \(\infty\), are identical at **every** time. In fact all mixed heat-kernel moments with at most four factors are identical, even when their times differ.

The same type of distinction occurs already in dimension four: for the two Conway–Sloane tori specified below, the difference, first minus second, is
\[
R_\alpha(T_-,t)-R_\alpha(T_+,t)
=2\alpha(\alpha-2)q^{86}+O_\alpha(q^{88}).
\]
Here the \(\pm\) labels refer only to the signs in the congruences below. This also proves generic distinction in the Conway–Sloane family by Shannon entropy, and by each fixed finite positive order other than 2.

## 1. Return counts and heat moments

Write \(u=p_t-1=\sum_{v\in\Lambda^*\setminus 0}q^{|v|^2}e^{2\pi i v\cdot x}\). Then
\[
\int_T u^j =
\sum_{\substack{(v_1,\ldots,v_j)\in(\Lambda^*\setminus0)^j\\\sum v_i=0}}
q^{\sum_i|v_i|^2}.
\]
Thus each coefficient counts ordered closed walks with a prescribed total squared length. With \(p_t\) instead of \(u\), zero vectors are included. For \(j\) times \(t_i>0\), the full mixed moment is the degree-\((j-1)\) Siegel theta series of \(\Lambda^*\) evaluated at
\[
Z=4\pi i\bigl[\operatorname{diag}(t_1,\ldots,t_{j-1})+t_j\mathbf1\mathbf1^\top\bigr],
\]
using the convention \(e^{\pi i\,\operatorname{tr}(\operatorname{Gram}(v)Z)}\). Indeed eliminate \(v_j=-\sum_{i<j}v_i\). Centered mixed moments follow by expanding the product of \(p_{t_i}-1\). This holds without an integrality hypothesis if the theta series is defined by its convergent sum.

The Milnor lattices are self-dual and their degree-\(d\) theta series agree for \(d=1,2,3\) (Witt, Igusa, Kneser; see [Hamilton, §1](https://arxiv.org/abs/2008.01043) for the precise statement). This proves all full and centered mixed moment equalities up to four factors. In particular orders \(2,3,4\) cannot distinguish. Order \(\infty\) is determined by the degree-one theta series because every Fourier coefficient is nonnegative, hence \(\|p_t\|_\infty=p_t(0)\).

In either comparison, at large \(t\) the mean-zero \(u\) is uniformly small by Gaussian summation. Shannon entropy expands in absolutely convergent powers of \(u\), with coefficient \((-1)^j/[j(j-1)]\) at \(u^j\) for \(j\ge2\). For \(\alpha\not=1\) expand \((1+u)^\alpha\) first, and then divide the log difference by \(\alpha-1\). The first nonzero moment discrepancy is multiplied by \(\binom\alpha j/(\alpha-1)\) at its order (including the continuous limit at 1). This is because both integrals \(\int (1+u)^\alpha\) start at 1 and have no linear term. These expansions justify extracting a coefficient without assuming the full heat kernels are equidistributed by value.

## 2. The first discrepancy for Milnor's tori

The first possible difference is at five factors; every nonzero squared length is an even integer at least 2. Thus the coefficient of \(q^{10}\) in \(\int u^5\) counts only roots, while terms of degree at least six are \(O(q^{12})\). Directly there are
\[
N_5(E_8\oplus E_8)=340139520,\qquad N_5(D_{16})=350461440
\]
ordered zero-sum five-tuples of roots. The sign and factor in the theorem follow by multiplying their difference \(10321920\) by \(\binom\alpha 5/(\alpha-1)=\alpha(\alpha-2)(\alpha-3)(\alpha-4)/120\).

Here are full finite count details. Use twice the ordinary coordinate roots, so all coordinates are integers. The \(D_n\) roots have two nonzero coordinates each equal to \(\pm2\); for \(E_8\) add the 128 vectors with eight entries \(\pm1\) and even negative parity. For \(D_{16}^+\) the glued half-integer coset has no norm-two vectors, so \(D_{16}\) gives its entire root shell. For a sum \(s\) put \(P(s)=\#\{(u,v):u+v=s\}\) and \(B(s)=\sum_r P(s-r)\), with \(r\) a root. Symmetry under negation gives \(N_5=\sum_s P(s)B(s)\). Enumerate ordered pairs to get \(P\); sum over the root list for \(B\). Signed permutations in \(D_{16}\), and permutations and even sign changes in \(E_8\), allow grouping by sorted absolute coordinates. For \(E_8\) record the sign parity in brackets only if every coordinate is nonzero, since a zero coordinate allows an extra sign change. That group acts transitively on every displayed type. The table lists cardinality of the group of sums and their two counts. The blank pattern is zero.

| Root set | Nonzero absolute coordinates of \(s\) | \(\#s\) | \(P(s)\) | \(B(s)\) |
|:--|:--|--:|--:|--:|
| \(E_8\) | none | 1 | 240 | 13440 |
| \(E_8\) | 4 | 16 | 14 | 1848 |
| \(E_8\) | 4,4 | 112 | 1 | 168 |
| \(E_8\) | 2,2 | 112 | 56 | 5253 |
| \(E_8\) | 2,2,4 | 1344 | 2 | 600 |
| \(E_8\) | \(2^4\) | 1120 | 14 | 1848 |
| \(E_8\) | \(2^6\) | 1792 | 2 | 600 |
| \(E_8\) | \(2^8\) [even] | 128 | 1 | 168 |
| \(E_8\) | \(1^8\) [even] | 128 | 56 | 5253 |
| \(E_8\) | \(1^7,3\) [odd] | 1024 | 14 | 1848 |
| \(E_8\) | \(1^6,3,3\) [even] | 3584 | 2 | 600 |
| \(D_{16}\) | none | 1 | 480 | 26880 |
| \(D_{16}\) | 4 | 32 | 30 | 2520 |
| \(D_{16}\) | 4,4 | 480 | 1 | 168 |
| \(D_{16}\) | 2,2 | 480 | 56 | 5973 |
| \(D_{16}\) | 2,2,4 | 13440 | 2 | 408 |
| \(D_{16}\) | \(2^4\) | 29120 | 6 | 936 |

Thus \(N_5(E_8)=137813760\). In \(E_8\oplus E_8\), a zero-sum tuple either lives in a single block or splits as two steps in one block and three in the other. Its count is \(2N_5(E_8)+2\binom52\cdot 240\cdot 13440\). The [independent exact replay](verify-heat-entropy-isospectral-tori.js) recomputes the table and also counts the two full 480-root sets directly, without orbit reduction, using injective balanced coordinate encoding and pair convolution. This gives the required count independently of the grouping.

## 3. A rank-four example and generic distinction

Take the two reciprocal lattices
\[
L_\epsilon=\{(x,y,z,w)\in\mathbb Z^4:z\equiv -x+y,\ w\equiv \epsilon(x+y)\pmod3\},\qquad \epsilon=-1,+1
\]
with the Euclidean inner product specified by the Gram matrix
\[
G=\begin{pmatrix}10&1&2&3\\1&10&-3&-2\\2&-3&10&-1\\3&-2&-1&10\end{pmatrix}.
\]
Here \(T_\epsilon=\mathbb R^4/L_\epsilon^*\) uses dual with respect to this product, and its harmonic frequencies are exactly \(L_\epsilon\). These are \(L_1,L_2\) in [Cerviño–Hein §§2.1–2.5](https://arxiv.org/abs/0910.2127), using \((r,\alpha,\beta,\gamma)=(10,1,2,3)\) in their Gram notation. Their two codes give the displayed congruences, and both lattices have the same theta series. The four orthogonal parameters in their §2.5 are \(1,3.5,3,2.5\), which are distinct and positive. Our sign notation does not relabel the article's \(L^\pm\).

Both shortest squared lengths are 18, and through total squared length 86 all centered fourth moments agree coefficientwise, whereas their centered third moments first differ at 86, with counts 12 versus 0. No fifth or higher power contributes through 86. Exact verification needs only vectors with squared norm at most 86 (indeed \(G\succeq 4I\), and the entries are integral, so each coordinate is between \(-4\) and \(4\)). For triangles, iterate ordered pairs \(u,v\) and check their third vector \(-u-v\) in the lists. The 12 hits at 86 are the permutations and overall signs of
\[
(-1,0,1,1),\quad (0,1,1,-1),\quad (1,-1,-2,0)
\]
of squared lengths \(18,30,38\). For fourth moments group ordered pairs by their vector sum and the sum of their squared norms, and convolve the squared-length counts for equal vector sums (the lists are sign-symmetric). The replay checks every coefficient, not merely the first triangular example. Since all squared lengths here are even integers, the next possible degree is 88. The entropic coefficient is \(12\binom{\alpha}{3}/(\alpha-1)=2\alpha(\alpha-2)\), and at \(\alpha=1\) it is \(-2\). Order \(2\) and order \(\infty\) are again equal at every time by the theta series.

For fixed \(t>0\) and fixed finite \(\alpha>0\), the entropy difference is real analytic on the open cone of positive-definite Gram parameters in the Conway–Sloane family (use a fixed parametrization of each torus and the uniform convergence of the differentiated Fourier series on compact parameter subsets). For \(\alpha\ne2\) it is not identically zero there: rescaling every Gram parameter simultaneously is equivalent to changing the time in the fixed example just analyzed. Its zero set therefore has empty interior and measure zero in parameter space. In particular for almost every parameter the analytic time difference is not identically zero, so the two entropy curves agree only at isolated times. The same analyticity in time justifies the isolated exceptional times for Milnor's pair at every stated order. This does not assert that a scalar entropy curve distinguishes every individual pair in the four-parameter family.

## Comparison

[Milnor's original isospectral example](https://www.pnas.org/doi/10.1073/pnas.51.4.542) has equal heat trace at every time. [Hamilton](https://arxiv.org/abs/2008.01043) uses energies of harmonic maps from tori, and [Mohades](https://arxiv.org/abs/2611.29403) uses direction-resolved averages along closed geodesics, both richer data than one scalar histogram functional. The distinction here requires neither marks nor directional observations: it appears in Shannon entropy of a single positive heat-kernel density, and the leading difference and all exceptional Rényi orders are explicit for the Milnor pair. These are statements about compact tori, not a lattice distinguishability algorithm for a cryptographic target.

Replay: Node.js 18+, no dependencies or data.
