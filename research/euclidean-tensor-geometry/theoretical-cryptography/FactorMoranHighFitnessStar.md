# The star uniquely maximizes birth–death Moran fixation at sufficiently high fitness

**Theorem.** Let \(n\ge3\). Consider all finite connected simple unweighted undirected graphs on \(n\) vertices, with no self-loops. In the usual birth–death Moran process, start with one uniformly chosen vertex of relative fitness \(r\), and all other vertices of fitness one. If
\[
                         r\ge384(n-1),
\]
the star \(K_{1,n-1}\) uniquely maximizes the probability of eventual fixation, up to isomorphism. For \(n\ge8\), the sufficient bound improves to \(r\ge64(n-1)\).

The thresholds are explicit sufficient bounds, not transition points. This is a finite-graph high-fitness extremum with \(r\) allowed to grow with \(n\). It does not claim an extremal theorem for fixed \(r\), weak selection, weighted graphs, temperature initialization, or death–birth updating. [Hindersin et al.](https://doi.org/10.1038/s42003-019-0374-x) studied numerical extremizers at specific fitness values; [Allen et al.](https://doi.org/10.1371/journal.pcbi.1008695) studied the derivative at \(r=1\); [Cuesta et al.](https://doi.org/10.1371/journal.pone.0200670) computed exact fixation functions and regime transitions through order seven. These are different from an all-order uniform high-fitness region. Strong amplifiers for fixed \(r>1\) and \(n\to\infty\), as in [Pavlogiannis et al.](https://arxiv.org/abs/1802.02509), are not contradicted. Our targeted literature and repository search did not locate the stated high-fitness theorem; that is not a priority guarantee.

## 1. Extinction equation and a uniform expansion

Write \(k=n-1\), \(z=1/r\), \(d_v=\deg(v)\), and \(t_v=\sum_{u\sim v}d_u^{-1}\). The numbers \(t_v\) are sometimes called vertex temperatures, but the initial vertex here is **uniform**, not temperature-weighted. Let \(q(S)\) be the extinction probability when the set of mutant vertices is \(S\). Thus \(q(\emptyset)=1\), \(q(V)=0\). Ignore all transitions that leave \(S\) unchanged. For a nonempty proper \(S\), define
\[
 B_w(S)=\sum_{\substack{v\in S\\v\sim w}}d_v^{-1},\qquad
 D_u(S)=\sum_{\substack{v\notin S\\v\sim u}}d_v^{-1},\qquad
 B=\sum_{w\notin S}B_w,\quad D=\sum_{u\in S}D_u.
\]
Both \(B,D\) are positive by connectedness. The choice of reproducing vertex with probability proportional to fitness followed by a uniformly chosen neighbor gives
\[
 (B+zD)q(S)=\sum_{w\notin S} B_wq(S+w)
                        +z\sum_{u\in S}D_uq(S-u).                 \tag{1}
\]
Every edge crossing the cut contributes one of \(1/d_v,1/d_u\) to each side, so \(D/B\le k\). For \(0<kz<1\), the embedded process has downward probability at most \(kz/(1+kz)\). Consequently \((kz)^{|S|}\) is a supermartingale up to absorption: the expectation multiplier is at most
\[
  \frac{kz}{1+kz}(kz)^{-1}+\frac{1}{1+kz}(kz)=1.
\]
Absorption occurs almost surely for this finite chain; from any proper nonempty set a sequence of increasing steps to \(V\) has positive probability. The supermartingale is bounded. Stopping at absorption yields
\[
                      0\le q(S)\le (kz)^{|S|}.                  \tag{2}
\]

For an adjacent pair \(u,v\), let
\[
 P_{uv}=\frac{(t_u-d_v^{-1})t_v+(t_v-d_u^{-1})t_u}
                    {2-d_u^{-1}-d_v^{-1}} .
\]
The denominator is the pair's \(B>0\). This is the sum of the weighted singleton first-order coefficients, divided by \(B\), over the two downward transitions from the pair. In particular \(0\le P_{uv}\le k^2\), using \(t_u,t_v\le k\), \(D/B\le k\). A singleton has \(B=1,D=t_v\). From (1)–(2), \(q(\{v\})\) differs from \(zt_v\) by at most \(k^2 z^2\): the direct extinction term is \(zt_v/(1+zt_v)\), and the remaining numerator has upper bound \(k^2 z^2\). Insert these singleton estimates into the pair equation. The upward term after dividing by \(B\) is at most \(k^3z^3\), and the signed error in the downward term is bounded by \(k^3z^3\) because \(D/B\le k\). Dividing the leading \(z^2P_{uv}\) by \(1+zD/B\) changes it by at most \(k^3z^3\), only in the downward direction. Therefore
\[
                    |q(\{u,v\})-z^2P_{uv}|\le 2k^3z^3.
\]
Now insert this in the singleton equation. In the upper bound the quadratic expansion of its direct term has error at most \(z^3t_v^3\), and not dividing the pair term by \(1+zt_v\) can only increase it. In the lower bound the direct quadratic expansion is a lower bound, and the division loses at most \(k^2z^3t_v\). Thus for the mean \(q_G=n^{-1}\sum_vq(\{v\})\),
\[
 \left|q_G-z-C_Gz^2\right|\le3k^3z^3,\qquad
 C_G=\frac1n\left[
   -\sum_v t_v^2+\sum_{uv\in E}(d_u^{-1}+d_v^{-1})P_{uv}
 \right].                                                       \tag{3}
\]
Here \(\sum_vt_v=n\) by exchanging the two vertex sums, which explains the identical first-order term for every graph. In the star \(t_v=k\) at the center and \(1/k\) at each leaf, and \(P_{uv}=1\) for each edge. Hence
\[
                             C_*=(n-k^2-1/k)/n.
\]
The expansion coefficient alone separates the star from every other graph. For \(n\ge7\) this follows already from the comparison below as \(z\to0\). For \(3\le n\le6\), direct exhaustive integer-rational computation of (3) gives the following table. The counts are labeled connected graphs, and the last column counts nonstars at the smallest coefficient gap.

| \(n\) | Connected graphs | \(\min_{G\not\cong K_{1,k}}(C_G-C_*)\) | Attaining graphs |
| ---: | ---: | ---: | ---: |
| 3 | 4 | \(1/2\) | 1 |
| 4 | 38 | \(269/252\) | 12 |
| 5 | 728 | \(851/600\) | 30 |
| 6 | 26704 | \(2139/1300\) | 60 |

This finite part suffices to distinguish the star for \(n\le6,\ r\ge384k\): by (3) the difference \(q_G-q_*\) is at least \(z^2(1/2-6k^3z)>0\) since \(k\le5\).

## 2. Retaining the first-step term makes the threshold linear in \(n\)

Put \(f(t)=zt/(1+zt)\). A nonstar has \(t_v\le k-1\) at every vertex. If its degree is at most \(k-1\), this uses each summand at most one. If its degree is \(k\), the vertex is universal, and some edge among its neighbors gives at least two terms at most \(1/2\). With \(\sum_vt_v=n=k+1\) and \(n\ge7\), the vector \((k-1,2,0,\ldots,0)\) majorizes its temperatures. The function \(f\) is concave on nonnegative arguments, so counting only direct extinction in (1) gives
\[
                           q_G\ge \frac{f(k-1)+f(2)}{n}.         \tag{4}
\]

For the star, use \(x_j,y_j\) for extinction from \(j\) mutant leaves with the center resident or mutant, respectively. The same two possible changing events in these states give
\[
 x_j=a y_j+(1-a)x_{j-1},\quad
 y_j=b y_{j+1}+(1-b)x_j,\quad
 a=(1+z/k)^{-1},\quad b=(1+kz)^{-1},
\]
with \(x_0=1,y_k=0\). The two equations apply for \(1\le j\le k\) and \(0\le j<k\), respectively. These are the usual star recurrences, also used for calculating its exact fixation probability; see [Broom–Rychtář](https://doi.org/10.1098/rspa.2008.0058). For a short bound let \(\lambda=(1-a)/b=z(1+kz)/(k+z)\). Eliminating the \(y_j\)'s gives \(x_{j+1}-x_j=\lambda(x_j-x_{j-1})\). From \(x_k=(1-a)x_{k-1}\),
\[
 x_j=1-\frac{\sum_{h=0}^{j-1}\lambda^h}{\,\sum_{h=0}^{k-2}\lambda^h+
                                                    \lambda^{k-1}/a\,}.
\]
For \(0<z\le1/(2k)\), \(k\ge2\), we have \(\lambda\le 3z/(2k)\le3/16\) and \(a^{-1}\le9/8\). The formula above gives \(x_j\le \lambda^j/[a(1-\lambda)]\) for \(1\le j\le k-1\) by bounding the numerator tail. For \(j=k\), this also follows because the numerator is then \(\lambda^{k-1}(1/a-1)=b\lambda^k/a\). Back-substitution in the \(y\) recurrence gives
\[
 y_2\le (1-b)\sum_{j=2}^{k-1}x_j
       \le\frac{kz\lambda^2}{a(1-\lambda)^2}
       <\frac{4z^3}{k}.
\]
The empty sum for \(k=2\) is consistent with \(y_2=0\). Since \(x_1=a y_1+(1-a)\), the \(y_1\) recurrence then gives \(y_1\le kz\,y_1+z^2+4z^3/k\). As \(kz\le1/2\), rearrangement yields
\[
 y_1\le z^2+(2k+8/k)z^3\le z^2+4kz^3.
\]
The mean \(q_*=(y_0+kx_1)/n\) therefore obeys
\[
                    q_*\le \frac{f(k)+kf(1/k)}n+z^2+4kz^3.     \tag{5}
\]

Subtract the first-step expressions in (4) and (5). Direct subtraction shows
\[
\begin{split}
 \frac{f(k-1)+f(2)-f(k)-kf(1/k)}{z^2}
 ={}&\frac{(2k-1)+k(k-1)z}{(1+kz)(1+(k-1)z)}\\
   &-\frac{4}{1+2z}+\frac{1/k}{1+z/k}\\
 \ge{}& 2k-5+1/k-\big((2k-1)^2+k^{-2}\big)z.
\end{split}
\]
For the last inequality use \(1/[(1+s)(1+t)]\ge1-s-t\) for nonnegative \(s,t\), and \(1/(1+z/k)\ge1-z/k\). The linear loss divided by \(n=k+1\) is less than \(4kz\). Combining with (4)–(5) gives
\[
                q_G-q_*\ge z^2\left(g_n-8kz\right),\quad
                g_n=\frac{n-7+1/(n-1)}{n}.                      \tag{6}
\]
For \(n=7\), \(g_7=1/42>8/384\). For \(n\ge8\), \(g_n>1/8=8/64\). The strict bound in both regimes proves uniqueness and completes the all-order comparison.

## Replay

Run `node verify_factor_moran_high_fitness_star.mjs` for the labeled exact census, and `python3 verify_factor_moran_high_fitness_star_independent.py` for an independent implementation. It recomputes the coefficient via cut-state branches rather than the closed edge formula and also solves the full rational absorption system for every connected labeled graph at orders 3 and 4 at two choices of \(r\). Those checks do not replace the uniform analytic estimates. This result concerns an abstract graph Markov process and does not specify any biological implementation.
