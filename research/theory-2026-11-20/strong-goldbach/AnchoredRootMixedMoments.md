# Beyond-floor mixed moments of the anchored paired sieve

Elementary complete Fourier orthogonality evaluates actual marked overlaps in the integer sieve for \(n\) and \(N-n\), at marked products **above the interval scale**. These give a natural-scale lower bound for genuine simultaneous rough-composite occupations, not for prime pairs.

Let \(N=2x\) be even, \(m=N-n\), and fix a nonnegative nonzero \(w\in C^\infty_c((1/2,3/2))\), with integral \(I_w\). Mark true primes in mutually disjoint fixed log-exponent bands. Partition left bands into two independent groups with respective products \(a,b\); let \(q\) be the product of all right labels. Retain \((abq,N)=1\). Define
\[
 {\cal C}_N(z)=\sum_{\substack{n,\ \mathrm{specified\ prime\ labels}\\
                     ab\mid n,\ q\mid m,\ (abq,N)=1}}w(n/x)1_{P^-(nm)\ge z}.
\]
Distinct bands make each group integer determine its labels. This is exactly the joint marked moment, with the given unit mask; repeated primes in the actual physical integers are not silently removed. Define
\[
{\cal H}=\sum_{\substack{\mathrm{labels}\\(abq,N)=1}}\frac1{abq},\qquad
V_{2,N}(z)=\prod_{p<z}(1-\nu_N(p)/p),\quad
\nu_N(p)=1+[p\nmid N].
\]

There are four examples of full support:

| Moment | left group 1 | left group 2 | right group |
|---|---|---|---|
| three tags | \([.279,.281]\) | \([.289,.291]\) | \([.459,.461]\) |
| four tags | \([.289,.291]\) | \([.309,.311]\) | \([.209,.211],[.229,.231]\) |
| six tags | \([.137,.139],[.149,.151]\) | \([.155,.157],[.169,.171]\) | \([.197,.199],[.219,.221]\) |
| deeper six tags | \([.1768,.1772],[.2098,.2102]\) | \([.1798,.1802],[.2118,.2122]\) | \([.1948,.1952],[.1998,.2002]\) |

For \(z=\exp((\log x)^{1/4})\), uniformly in the target,
\[
 {\cal C}_N(z)=x I_w V_{2,N}(z){\cal H}+O_{A,w}(x(\log x)^{-A})
 \quad\text{for every fixed }A.
\]
For fixed sufficiently small \(\eta>0\), \(z=x^\eta\), the same formula holds with relative error \(O_w(H^{-H/2})+o_\eta(1)\) on the positive main, \(H=.005/\eta\). Consequently for some fixed \(\eta>0\), in *every* sufficiently large even \(N\) there are \(\gg_\eta \mathfrak S(N)x/(\log x)^2\) distinct actual pairs with both legs \(x^\eta\)-rough and satisfying every specified true factor band. Indeed \(V_{2,N}(z)\sim e^{-2\gamma}\mathfrak S(N)/(\log z)^2\), \({\cal H}\) tends to the product of positive prime Mertens harmonic band integrals, and the weight and the number of eligible labels per physical integer are both bounded. The tuple products exceed \(x^{1.027},x^{1.036},x^{1.026}\), and \(x^{1.1728}\), respectively; a CRT per-row floor bound is not sufficient.

## Exact products and nonzero frequencies

Use [Koukoulopoulos' dimension-two fundamental lemma, Theorem 19.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf#page=206) with level \(D=x^\tau,\ \tau=.005\). Its product condition is uniform by Mertens, \(\nu_N(p)\le2\) and \(\nu_N(2)=1\). For \(e\mid nm\) in a squarefree sieve label, use disjoint splits \(e=e_1e_2\) for the roots \(0,N\). At \(p\mid N\) there is only one root, assigned to \(e_1\). Each term counts
\[
 n=ab e_1 j,\qquad j\equiv N\overline{ab e_1}\pmod{q e_2},
\]
with exact coprimality of \(ab e_1,q e_2\), since bands are disjoint and above the presieve. There is no extra unit test on the free integer \(j\). Poisson gives
\[
 \frac{x}{abqe}\sum_h
   \widehat w(hx/(abqe))\,e_{q e_2}(hN\overline{ab e_1}).
\]
Its zero term is exactly \(x I_w/(abqe)\).

Fix dyadic scales \(a\asymp A_0,b\asymp B_0,q\asymp Q\), and put
\(\alpha=\log_x(A_0B_0)\), \(\beta=\log_x Q\).
At each corner of the four respective exponent boxes, with strict room for \(o(1)\) dyadic displacements,
\[
 \alpha+\beta>1,\quad \max(\log_x A_0,\log_x B_0)<\beta,\quad
 \alpha/2+3\beta/2+3\tau/2<1,\quad
 \alpha+\beta-1+\tau+.01<\min_{\text{right }r}\log_x r .              \tag{1}
\]
The maxima in the third inequality are \(.985,.9715,.9465,.9905\). Truncate \(|h|\le (A_0B_0Qe/x)x^{.01}\) with an arbitrarily power-small error by Schwartz decay. For nonzero retained \(h\), the last inequality makes \(h\) a unit modulo the actual product \(q\), since it is smaller than each genuine prime factor. By CRT the \(q\)-phase is \(e_q(C\bar a\bar b)\), \(C=hN\overline{e_1e_2}\) a unit. Split only \(a\) by its residue modulo \(e_2\), so that the other CRT component becomes a bounded coefficient in \(b\) alone. Both \(a,b\) inject into units modulo \(q\) after inversion, by (1). The full matrix \((e_q(Cuv))_{u,v\bmod q}\) has norm \(\sqrt q\) by ordinary Fourier orthogonality, also for composite \(q\). On any subrectangle in one \(a\)-class it bounds the bilinear sum by \(\sqrt q\,(\#a)^{1/2}\sqrt{2B_0}\). Cauchy over classes therefore gives \(\ll\sqrt{qA_0B_0e_2}\). This uses no theorem for an additive rank-one reciprocal trace.

Two-variable partial summation restores the Poisson weight. Its value and scaled first/mixed derivatives on the factor rectangle are bounded by \(O_{w,J}(\frac{x}{A_0B_0Qe}(1+|h|x/(A_0B_0Qe))^{-J})\); summing over all nonzero \(h\) costs \(O_w(1)\). The discarded large frequencies, including nonzero multiples of the genuine right primes, are also controlled absolutely by the stated decay. Summing the \(q\)'s costs \(O(Q)\), by disjoint labelled right bands. The sieve labels and their splits cost at most \(\sum_{e\le D}2^{\omega(e)}\sqrt e\ll D^{3/2}\log(2D)\). Thus the whole nonzero part is \(\ll Q^{3/2}\sqrt{A_0B_0}D^{3/2}L^{O(1)}\), with a fixed power margin by (1).

For the zero modes multiply by \(\lambda_e^\pm\), then sum the exact \(\nu_N(e)\) root assignments. The fundamental lemma gives the two bracketing principal values \(V_{2,N}(z)(1+O(H^{-H/2}))\), \(H=\log D/\log z\). This saving is arbitrary-log for subpower \(z\). At fixed polynomial \(z\), choose \(H\) large independently of \(N\). The local product comparison uses the sole root at 2 and the actual roots at odd primes dividing \(N\); factors omitted at \(p\ge z\) have ratio \(1+O(L/z)\), uniformly. Excluding macro labels dividing \(N\) also loses only a power-small harmonic. This proves the results.

## Use and limits

These actual joint overlaps can enter the anchored pair's Bonferroni/factorial moment accounting as **natural-scale nonzero terms**, even at six marks and beyond the floor-summing cutoff. They are not captured by separate one-leg bounds. This differs from earlier subcritical prime-product spectral notes, which retained free-factor arithmetic weights and did not produce this integer anchored sixth moment. It also differs from the genuine same-cofactor prime/semiprime comparison, which has an extra primality constraint and different exponents.

[Ziller--Morack's paired Jacobsthal reduction](https://arxiv.org/abs/1706.00317) is the covering context. The [September Plectis one-class proposal](https://wcook04.github.io/plectis-atlas/papers/A-quadratic-bound-for-Jacobsthals-function-September-25-2026.html) has a scalar one-color sieve boundary near parameter 2, not a positive two-color boundary. Our calculation treats selected mixed prefixes of the actual anchored roots, not the complete signed tree. In particular many profiles where both grouped products exceed the square root are outside (1), and the free cofactors here are not forced to be primes. No lower bound for prime-pair survival follows.

The deeper example uses a strict crossing of more than .17 in log exponent. Abstractly the two length conditions \(\alpha<2\beta\) and \(\alpha+3\beta<2-3\tau\) permit the sum to approach \(6/5\) as \(\tau\downarrow0\), but that algebra does not supply a general covering of all root profiles or a prime count.

[check_anchored_root_mixed_moments.py](check_anchored_root_mixed_moments.py) checks every numerical box corner by exact rational arithmetic.
