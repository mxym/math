# Antipodal-pair tradeoffs above 72 and 126 kissing points

Let $C\subset S^{n-1}$ be any finite set with $x\cdot y\le 1/2$ for distinct points. Count an antipodal pair $\{x,-x\}$ only once. The following are **upper bounds on the number of pairs in a code of the indicated size**, not assertions that such a code exists.

| Dimension | Number of points | Maximum number of pairs is at most |
|---|---|---|
| 6 | 73, 74, 75, 76 | 27, **24, 22, 20**, respectively |
| 7 | 127, 128, 129, 130, 131, 132 | 54, **51, 49, 47, 46, 45**, respectively |

No lattice, root-system, or extension-to-a-particular-projective-code assumption is made. The first entries were obtained in [the earlier first-excess estimate](KissingAntipodalPairTail.md); the additional entries bound how the antipodal-pair count must fall with cardinality. These do not settle either unrestricted kissing number. The classical antipodal capacities are due to [Anstreicher](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf). Here is a self-contained derivation of all the displayed bounds using a weighted zonal kernel and a low-dimensional local moment certificate.

## 1. A necessary weighted-energy inequality

Set $P=36$ if $n=6$, and $P=63$ if $n=7$. Write $|C|=2P+r$, $p=$ number of pairs, $s=P-p$, and $q=2s+r=$ number of singletons. Use
$$
f(t)=t^4-\tfrac14 t^2,\qquad
F(t)=f(t)+\tfrac{46}{100}t^5+\tfrac{26}{100}t^3-\tfrac{81}{1000}t .
$$

Both kernels have nonnegative coefficients in normalized spherical Gegenbauer polynomials ($P_k(1)=1$). For clarity: $f$ has constant coefficient $f_0=(10-n)/(4n(n+2))=3/(4P)$, degree-two coefficient $(n-1)(6/(n+4)-1/4)/n>0$, and positive leading coefficient. The degree-one coefficient in the odd part of $F$ is $-81/1000+(26/100)3/(n+2)+(46/100)15/((n+2)(n+4))>0$; its remaining odd coefficients are positive by the three-term recurrence for $tP_k$. The addition formula therefore gives $\sum w_xw_y F(x\cdot y)\ge f_0(\sum w_x)^2$ (and likewise for $f$).

Any collection of lines with mutual absolute inner products at most $1/2$ has size at most $P$: apply the same inequality for $f$ to one unit representative per line, use $f(1)=3/4$ and $f\le0$ on $[-1/2,1/2]$. In particular $p\le P$; $p=P$ is impossible when $r>0$ because a singleton would give one more line.

Weight each paired point by $1/2$, each singleton by $\alpha=s/q$. The total weight is $P$. Between two different paired axes, or between a paired axis and a singleton, the odd terms cancel and the even terms are nonpositive. Each paired axis contributes $f(1)=3/4$ within itself. Thus, summing over **ordered** distinct singleton indices,
$$
 F(1)+\frac1q\sum_{i\ne j} F(x_i\cdot x_j)\ \ge\ \frac{3q}{4s}. \tag{1}
$$

## 2. A singleton and its negative neighbors

For the specified size, consider a code with the largest attainable number of pairs. Join singletons $x,y$ when $x\cdot y<-1/2$. This graph is triangle-free, since the squared norm of the sum of three unit vectors in a triangle would be negative. Neighbors of any vertex thus give independent lines, together with the $p$ paired axes, so its degree $d$ is at most $s$. Also $d\ge2$: if $x$ has just one neighbor, replace that neighbor by $-x$. If it has none, remove any other singleton and add $-x$. Either preserves the size, preserves all pairs, and creates one. There is another singleton since $s,r\ge1$.

Fix $x$ and let $a_i=-x\cdot y_i\in(1/2,1)$ for its $d$ neighbors. Choose the unique solution to $\sum_i(a_i-m)_+=m$, and put $v_i=(a_i-m)_+$. Cauchy–Schwarz and $y_i\cdot y_j\le1/2$ give
$$
 \left(\sum_i v_i a_i\right)^2
 \le \left\|\sum_i v_i y_i\right\|^2
 \le \tfrac12\left(\sum_i v_i^2+(\sum_i v_i)^2\right).
$$
But $\sum_i v_i a_i=\sum_i v_i^2+m^2>0$. Consequently $\sum_i v_i^2+m^2\le1/2$. The bounds $\sum_i v_i\ge d(1/2-m)$ and $\sum_i v_i^2\ge m^2/d$ imply
$$
 \frac{d}{2(d+1)}\ \le m\le\ \sqrt{\frac{d}{2(d+1)}}. \tag{2}
$$
At most $n_d=\min(d,7)$ values $a_i$ can reach $u=725/1024>1/\sqrt2$: the projections $y_i+a_i x$ of these neighbors into $x^\perp$ have pairwise strictly negative dot products. An obtuse set in $\mathbb R^{n-1}$ has at most $n$ members: otherwise affine dependence would equate positive and negative convex combinations on disjoint, nonempty supports, whose dot product would simultaneously be nonnegative and strictly negative.

## 3. The exact local certificate

The excess thresholds we exclude are $(r,S_r)=(1,8),(2,11),(3,13),(4,15),(5,16),(6,17)$: for these values we show $s>S_r$. Put $H=4/625$ and let $U_d$ be the following rational numbers (numerators over $100000$).

| $d$ | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| $10^5U_d$ |11258|11898|12538|13178|13818|14458|15098|15738|
| $d$ |10|11|12|13|14|15|16|17|
| $10^5U_d$ |16378|17018|17658|18298|18938|19578|21736|23489|

The [standalone exact checker](verify-kissing-antipodal-tradeoff.js) verifies $F(t)\le H$ for $|t|\le1/2$. For a degree $d$, on each of a few rational intervals covering (2), it supplies constants $B,J\ge0$ and $D\in\mathbb R$ and verifies, for every $a\in[1/2,1]$ and $m$ in that interval, with $v=(a-m)_+$,
$$
 dF(-a)+ B(1/2-m^2-dv^2)+D(m-dv)
       +J\big(n_d-d\,\mathbf1_{a\ge u}\big) < U_d. \tag{3}
$$
Averaging (3) over the $d$ neighbors gives $\sum_i F(-a_i)<U_d$: the $B,J$ terms have nonnegative averages and the $D$ term has average zero. Every nonneighbor contributes at most $H$. Thus each singleton row is strictly less than $U_d+(q-1-d)H$. Finally the checker verifies, by integer multiplication, for every $1\le s\le S_r$ and $2\le d\le s$,
$$
 F(1)+U_d+(q-1-d)H < 3q/(4s),\qquad F(1)=1389/1000.
$$
This contradicts (1), proving the claims.

**Replay.** Run `node verify-kissing-antipodal-tradeoff.js` (no dependencies). The certificate list contains the exact interval endpoints (denominator $65536$) and multipliers (denominator $100000$). On each rectangle it uses tensor-product Bernstein coefficients of bidegree $(5,2)$ as rigorous upper bounds, bisecting if necessary. Rectangles that straddle $a=m$ must certify both polynomial branches; at $a=u$ the two closed-side tests include the correct convention. The integer grid only specifies exact rational *subdivision endpoints*; interiors are proved by the Bernstein convex-hull property, not sampled. The search for multipliers is not needed for replay. As a cross-check, the same certificate was separately recomputed in rational Python arithmetic by interpolating on a 6-by-3 tensor grid, inverting the Bernstein evaluation matrices, and bisecting via de Casteljau.
