# Near contacts forced by a hypothetical 76-point kissing code in six dimensions

A 76-point kissing code in $\mathbb R^6$, with **no symmetry assumption**, must have many pairs close to a contact: 384 unordered pairs with inner product above $0.480$, 287 above $0.485$, and 88 above $0.490$. In angle language, the last count concerns pairs at angles from $60^\circ$ up to (but not including) $\arccos(0.490)$. These need not be exact contacts.

| Inner product strictly above | Unordered pairs, at least |
|---:|---:|
| 0.480 | 384 |
| 0.485 | 287 |
| 0.486 | 259 |
| 0.487 | 226 |
| 0.488 | 188 |
| 0.489 | 143 |
| 0.490 | 88 |
| 0.491 | 21 |
| 0.4911 | 14 |
| 0.4912 | 6 |
| 0.49125 | 2 |

This is a structural consequence of [Tejasvi Singh Tomar's published four-point certificate](https://www.mefyi.com/papers/kissing-numbers-five-seven/), not a second independent proof of the 76 upper bound. It neither constructs nor excludes a 76-point code, and claims no optimality for these integers. [Musin, §§4–5](https://arxiv.org/html/2309.13854v4) explains the existing principle of extracting distance information from multipoint certificates, including the pair contribution for the 24-cell. Here we retain **both the pair slack and the full trivial-representation quadratic energy** of the six-dimensional certificate, then combine a supporting plane of that energy with positive two-point harmonics. The proof works on continuous intervals.

## A residual inequality with the correct multiplicities

Set $N=76$, $q=\binom N2=2850$, $M=7699/100$. Write $m_j=\sum_{\{x,y\}}(x\cdot y)^j$ and $v=(1,N,m_0,\dots,m_{10})$; all pair sums are over **unordered** two-element subsets. Let $F,a,X,Y$ be the blocks named `dense_0_0`, `dense_sos1`, `dense_sos2_1`, `dense_sos2_2` in the author's `6_76` archive. The scalar block is identified with its sole entry. With $T_j$ the ordinary Chebyshev polynomials and $c_j=(T_0,\ldots,T_j)^T$, put
\[
 R(u)=c_{10}(u)^TXc_{10}(u)+(1+u)(1/2-u)c_9(u)^TYc_9(u).
\]
Then
\[
             v^TFv+Na+\sum_{\{x,y\}}R(x\cdot y)\ \le\ M-N.\tag{1}
\]

Here is the normalization check. In the [de Laat–Leijenhorst–de Muinck Keizer formulation, §4](https://arxiv.org/html/2404.18794v2#S4), the index family consists of the empty set, singletons and unordered pairs. Sum the kernel over all *ordered* pairs of such subsets and group by their union. The empty-union value is at most $M$; singleton, pair, triple and quadruple contributions have certified slacks against $-1,0,0,0$, respectively. Thus total kernel energy plus the slack terms is at most $M-N$. The singleton/pair slacks are exactly $a,R$; the other two are nonnegative on realizable subconfigurations. The total kernel energy is a sum of nonnegative representation energies. For the trivial representation the zonal inner product is one. The sole empty/singleton bases are 1; the two-element bases are $u^j$ in ascending $j=0,\ldots,10$ (the pair's internal product). Summing the features before applying $F$ gives $v^TFv$, with no doubling of $m_j$. The identity transforms and multiplier/basis files in the original certificate are included in the optional source digest check. The original formulation and code are also in the [authors' data archive](https://doi.org/10.4121/74ce1c25-6fca-4680-8a36-e9c18e7e9594.v1).

## From one supporting plane to integer pair counts

For any rational vector $z$, $v^TFv\ge 2z^TFv-z^TFz$ because $F\succeq0$. Write $b=Fz$ and $P_j$ for the dimension-six normalized Gegenbauer polynomial ($P_j(1)=1$). Its positive kernel gives $-\sum_{\{x,y\}}P_j(x\cdot y)\le N/2$. For rational $\lambda,h_j\ge0$ define
\[
 p(u)=\lambda\left(R(u)+2\sum_{j=0}^{10} b_{j+2}u^j\right)-\sum_{j\ge1}h_jP_j(u),
 \qquad B=\lambda\big(M-N-Na+z^TFz-2b_0-2Nb_1\big)+\tfrac N2\sum_j h_j.
\]
Indices of $b$ start at zero. By (1), $\sum p(x\cdot y)\le B$. If $l$ is a lower bound for $p$ on $[-1,t]$ and for $1+p$ on $[t,1/2]$, then the number of pairs **strictly** above $t$ is at least $\lceil ql-B\rceil$. The endpoint $u=t$ is covered by the former condition, so no pair at $t$ is spuriously counted.

The [witness](kissing-six-near-contact-certificate.json) includes the nonnegative multipliers and the rational tangent point for each threshold. Its compact source matrix entries use integer endpoints scaled by $10^{24}$. Use their lower endpoints in $p,B$, but add to $B$ the conservative error allowance
\[
 \lambda\,\frac{2}{10^{24}}\Big(\|z\|_1^2+2\|z\|_1(1+N+11q)+221q+N\Big).
\]
Indeed every entry differs from its lower endpoint by at most $2\cdot10^{-24}$, $|m_j|\le q$, $|T_j|\le1$, and $0\le(1+u)(1/2-u)\le1$. The 221 terms are $11^2+10^2$. This does **not** assume that the rounded matrix is positive semidefinite; the supporting-plane inequality is applied to the original exact matrix before perturbation. All interval extrema are bounded by exact Bernstein coefficients on rational subdivisions. Only the integer ceiling is used in the table.

## Local meaning, and a consequence for size 75

For every vertex of any such code, the number of neighbors above $0.480$ is at most **26**, and above $0.490$ at most **25**. In fact this cap bound does not require $N=76$. Project these neighbors to the unit sphere of $x^\perp\subset\mathbb R^6$. For heights $a,b\in(t,1/2]$ their projected product is at most $(1/2-ab)/\sqrt{(1-a^2)(1-b^2)}$, decreasing in each height in the given range (the sign of the $a$ derivative is the sign of $a/2-b$). Thus their products are at most $s=(1/2-t^2)/(1-t^2)$. The verifier constructs a dimension-five normalized Gegenbauer polynomial $1+\sum h_jP_j$ with $h_j\ge0$, tests it is negative throughout $[-1,s]$ and gives $f(1)<27$ or $<26$, respectively. The usual positive-kernel sum bounds the number of neighbors by $\lfloor f(1)\rfloor$. In particular the projections cannot coincide, since $s<1$.

At size 76, at least one point has eleven neighbors above $0.480$ (sum the degrees). By Vizing's simple-graph edge coloring theorem there are at least $\lceil384/(26+1)\rceil=15$ **disjoint** such pairs. The analogous count is at least 11 disjoint pairs above $0.485$, and 4 above $0.490$.

Finally, if a 75-point code fails to contain 36 disjoint strict *negative* pairs (product below $-1/2$), the [antipodal extension theorem](https://github.com/mxym/math/blob/5c34aa6bc59244f3ed2a33ea1b224ae6d5b7b2a0/research/euclidean-tensor-geometry/KissingSixSeventyFiveExtension.md) embeds it into a 76-point code by adding one vertex. Deleting that vertex costs at most its cap degree. The 75 original points must therefore have at least **358** pairs above $0.480$, **261** above $0.485$, and **63** above $0.490$. The strict negative pairs and these positive near-contact pairs are different objects.

**Replay.** Run `python3 verify_kissing_six_near_contacts.py` with the neighboring JSON (Python 3.9+ standard library). Add `--source proof_6_76.tgz` for an integer-by-integer check against the [original exact CC BY 4.0 source](https://doi.org/10.5281/zenodo.24093810); `--source download` streams the corresponding [v3 release archive](https://github.com/tejasvi/kissing-numbers-lasserre/releases/download/v3/proof_6_76.tgz), about 767 MB. The compact matrices here are outward-rounded adaptations of Tomar's data. This optional step checks all 391 inclusions and 12 source file hashes, not the full semidefinite certificate; for the latter use the verification package linked by Tomar.
