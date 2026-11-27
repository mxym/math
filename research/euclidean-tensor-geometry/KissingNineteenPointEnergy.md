# A 19-point energy bound for kissing codes in dimensions six and seven

For any 73-point kissing configuration in $\mathbb R^6$, at most **26** pairs can be antipodal. For any 127-point configuration in $\mathbb R^7$, at most **53** can be antipodal. The axes are arbitrary: no crystallographic, integrality, or root-frame hypothesis is used. The same exclusions hold for disjoint pairs within the explicit tolerances below. These are restrictions on counterexamples, **not** unrestricted kissing-number upper bounds.

Normalize every point to unit length; different code points have inner product at most $1/2$. Put $f(t)=t^4-t^2/4$. The main certificate is a uniform bound for **any** 19-point kissing code $Y$ in the indicated dimension, with the diagonal included:

| Dimension $n$ | Upper bound $U_n$ for $\frac1{19}\sum_{y,z\in Y}f(y\cdot z)$ | Forbidden number $p$ of marked pairs | Allowed error $\|x+y\|$ for each marked pair |
|---|---|---|---|
| 6 | $3154135879149453/2000000000000000$ | 27 pairs among 73 points (54 endpoints) | $\le 1/3000$ |
| 7 | $1577227253193267/1000000000000000$ | 54 pairs among 127 points (108 endpoints) | $\le 1/6000$ |

Both energy bounds are strictly below $19/12$. The angular error from exact opposition is exactly $2\arcsin(\|x+y\|/2)$. Compare the [previous exact-pair tradeoff](KissingAntipodalTradeoffSixSeven.md) and [near-antipodal tail](KissingNearAntipodalTail.md), which also give other count/tolerance tradeoffs.

## Why 19 points suffice

Write $q=19$, $s=9$, $P=p+s$ (36 or 63). The constant spherical harmonic of $f$ is $f_0=3/[n(n+2)]-1/(4n)=3/(4P)$. The remaining Gegenbauer coefficients are nonnegative: the degree-four leading coefficient is positive and the coefficient of the degree-two harmonic has the sign of $6/(n+4)-1/4>0$. The spherical addition formula therefore gives $\sum w_i w_j f(x_i\cdot x_j)\ge f_0(\sum_i w_i)^2$.

For exact antipodal pairs keep one representative of each pair with weight one, and give each residual point weight $s/q$. Every nondiagonal interaction involving a representative has $|t|\le1/2$, so $f(t)\le0$. The weighted inequality would require
\[
 f_0P^2\le 3p/4+(s^2/q)U_n,\qquad U_n\ge 3q/(4s)=19/12.
\]
This argument selects only the marked pairs; any extra antipodes in the remaining 19 points are allowed.

For the approximate version write each marked pair as $m_i\pm r_i e_i$ with $\|m_i\|\le h$, $e_i$ unit, $r_i^2=1-\|m_i\|^2$. Average the two endpoint inequalities having the same sign product between pairs, for each choice of the sign product. It follows that $(e_i\cdot e_j)^2\le A=((1/2+h^2)/(1-h^2))^2$. The two endpoint inequalities against a residual point $y$ similarly give $(e_i\cdot y)^2\le C=(1/2+h)^2/(1-h^2)$. With $\phi(u)=u(u-1/4)$ and $A,C\ge1/4$, we have $f(t)\le\phi(A)$ or $\phi(C)$ on these intervals, respectively. The same weights now require
\[
 0\ge 3s/4-(s^2/q)U_n-p(p-1)\phi(A)-2ps\phi(C).
\]
The replay checks that the right side is strictly positive at $h=1/6000$ in dimension six and $h=1/12000$ in dimension seven.

## The energy certificate

We use the positive three-point kernels of [Bachoc and Vallentin](https://arxiv.org/abs/math/0608426). The inputs in the [standalone replay](verify-kissing-nineteen-point-energy.js) are two compressed JSON records, each giving the dimension, point count, degree, common denominator $10^8$, coefficients of $h_0$ and $g$, a constant $B$, and integer rectangular Gram factors. Here $h_0(t)$ is a nonnegative-coefficient combination of positive-degree normalized Gegenbauer polynomials in dimension $n$; it has no constant term in that basis. The coefficients of $g$ are in the Chebyshev basis $T_i$.

For $a=x\cdot y,b=x\cdot z,c=y\cdot z$, write $w=c-ab$, $v=(1-a^2)(1-b^2)$, and define $Q_0=1$, $Q_1=w$,
\[
 Q_{k+1}=((2k+n-3)wQ_k-kvQ_{k-1})/(k+n-3).
\]
These are homogenized Gegenbauer kernels in the $(n-1)$-dimensional space $x^\perp$. For each column of factor $k$, let $u$ be the Chebyshev polynomial with coefficients that column divided by $10^8$. Sum $u(a)u(b)Q_k$ across columns and $k$, then average over the three choices of anchor to obtain the symmetric polynomial $S(a,b,c)$. For each fixed anchor, the addition formula on projected vectors gives positive semidefiniteness, including zero projections by homogeneity or continuity. Thus its ordered triple sum is nonnegative; the ordered pair sum of $h_0$ is likewise nonnegative.

The replay verifies two polynomial inequalities, with $\epsilon=1/40000,\eta=1/200000$:

1. $S(a,b,c)\le g(a)+g(b)+g(c)+\epsilon$ when $a,b,c\in[-1,1/2]$ and the Gram determinant $1+2abc-a^2-b^2-c^2$ is nonnegative.
2. $f(t)+h_0(t)+3S(1,t,t)+3(q-2)g(t)\le B+\eta$ throughout $[-1,1/2]$.

Add the two nonnegative sums to the ordered $f$ energy. Triples with exactly two equal indices contribute $3S(1,t,t)$ per ordered off-diagonal pair; across triples of distinct indices the three $g$ terms contribute $3(q-2)g(t)$ per such pair. Dividing by $q$ gives the exact upper bounds in the table:
\[
 f(1)+h_0(1)+S(1,1,1)+(q-1)(B+\eta)+(q-1)(q-2)\epsilon .
\]

**Exact replay:** run `node verify-kissing-nineteen-point-energy.js`. The verifier expands the given Gram factors in rational arithmetic and converts the local slack polynomials to tensor Bernstein form on $[-1,1/2]^d$. On the initial box, lower coefficients are rounded down to a fixed dyadic grid and determinant upper coefficients up. Repeated midpoint de Casteljau subdivision rounds outward; its stored dyadic numerators and all intermediate sums are within the exact-integer range (a checked initial $2^{50}$ bound on each numerator is preserved by averaging). A box is accepted if all slack lower coefficients are nonnegative, or rejected as outside if every determinant upper coefficient is negative or it is disjoint from $a\le b\le c$. Symmetry justifies the ordering. A resource or arithmetic guard aborts rather than accepting an unresolved box. The one-variable checks visit 3 nodes each; the triple checks visit 561 and 603 nodes, respectively. No optimizer, package install, or numerical tolerance is needed for replay.
