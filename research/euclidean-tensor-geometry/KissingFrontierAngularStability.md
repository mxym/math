# Angular and integral-rank stability at the first excess kissing number

Suppose that 73 unit vectors in dimension six, or 127 in dimension seven, have mutual inner products at most $1/2$. The [19-point energy bound](KissingNineteenPointEnergy.md) allows at most $p=26$ or $53$ antipodal pairs. What if this maximum is attained? The following restrictions use **no root-frame or integrality hypothesis**.

Choose representatives $u_i$ from the $p$ antipodal pairs. Let $y_j$ be the remaining 21 points. Count an axis–axis pair once, and an axis–residual pair once. Call either kind **middle** if the absolute inner product belongs to $[1/4,\sqrt3/4]$. For the $p$ representative axes form $G=(2u_i\cdot u_j)$, and round its entries to the nearest integer to obtain a symmetric $H$ (ties may be settled either way, symmetrically).

| Dimension | Marked axes | Middle axis–axis pairs | Middle pairs of either kind | $\|G-H\|_F^2$ | $\operatorname{rank}H$ |
|---:|---:|---:|---:|---:|---:|
| 6 | 26 | at most 1 | at most 3 of 871 | $<0.940$ | **at most 12** |
| 7 | 53 | at most 2 | at most 5 of 2,491 | $<1.252$ | **at most 13** |

For example, in dimension six, if there is a middle axis–axis pair, at most one axis–residual pair is middle. These are necessary conditions for a counterexample with exactly that many antipodal pairs, **not** an exclusion of that counterexample. $H$ is an integer matrix with diagonal 2 and other entries in $\{0,\pm1\}$; it is **not assumed positive semidefinite** or treated as a root Gram matrix. The rank bound gives a rational kernel of dimension at least 14 or 40.

## 1. A weighted deficit estimate

Write $n$ for the dimension, $q=21$, $\gamma=10/21$, $P=p+10$. Put $f(t)=t^4-t^2/4$, $d(t)=-f(t)$. For any $q$ kissing points in the indicated dimension the following bounds include all diagonal terms:

\[
E_q=q^{-1}\sum_{j,k} f(y_j\cdot y_k)\ \le U_n,\qquad
U_6=\frac{9505462750363939}{6000000000000000},\quad
U_7=\frac{71429523091691371}{45000000000000000}.
\]

The [exact verifier](verify-kissing-frontier-angular-stability.js) includes two rational Gram-factor charts. They use the [three-point energy derivation](KissingNineteenPointEnergy.md#the-energy-certificate), based on the positive semidefinite spherical kernels of [Bachoc and Vallentin](https://arxiv.org/abs/math/0608426). The verifier reconstructs the kernels from positive Gram factors and nonnegative scalar weights. It checks the pair polynomial on $[-1,1/2]$ and the symmetric triple polynomial, in sorted coordinates, on the full feasible Gram domain by outward-rounded integer Bernstein subdivision. The chart slacks $(\epsilon,\eta)$ are $(1/750000,1/100000)$ and $(1/150000,1/90000)$. A separate reconstruction using closed-form Gegenbauer polynomials and reversed-coordinate Bernstein subdivision yielded the same exact bounds.

Give each $u_i$ weight one and each $y_j$ weight $\gamma$. The weights sum to $P$. Define

\[
M=\sum_i u_i u_i^T+\gamma\sum_j y_j y_j^T,\quad
c_n=\frac6{n+4}-\frac14,\quad f_0=\frac{10-n}{4n(n+2)}.
\]

The polynomial $f$ is the sum of $f_0$, $c_n(t^2-1/n)$, and the monic degree-four spherical harmonic kernel $t^4-6t^2/(n+4)+3/((n+2)(n+4))$. The last has nonnegative weighted double sum by the addition formula; the quadratic kernel has sum $\|M-(P/n)I\|_F^2$. Since both signs of every marked axis are present, all off-diagonal products involving an axis have absolute value at most $1/2$. Splitting the ordered double sum and using $f_0P^2-3p/4=15/2$ gives, with all three terms nonnegative,
\[
2\sum_{i<k}d(u_i\cdot u_k)+2\gamma\sum_{i,j}d(u_i\cdot y_j)
+c_n\|M-(P/n)I\|_F^2
\le\Delta_n=\frac{100}{21}U_n-\frac{15}{2}.
\]
In the interval defining middle pairs, $d(t)\ge3/256$: write $d=t^2(1/4-t^2)$ and check the two endpoints in $t^2$. If $A,B$ respectively count the two kinds of pairs then $(3/256)(2A+2\gamma B)\le\Delta_n$. Integer rounding gives the table.

## 2. Integer approximation and singular values

On $0\le t\le1/2$,
\[
d(t)\ \ge\ \frac{3}{16}\min\{t,1/2-t\}^2.
\]
For $t\le1/4$ divide by $t^2$; for $1/4\le t<1/2$ use that $t^2(1/2+t)/(1/2-t)$ is increasing. Both endpoints where the divisor vanishes are immediate. Applying this to every off-diagonal entry, including both orders, gives $\|G-H\|_F^2\le D=(64/3)\Delta_n$. Upper rational bounds $D_*=47/50,313/250$ respectively give the table.

Let $r=\operatorname{rank}H$ and suppose $r>n$. Denote the singular values by $\sigma_i$ in decreasing order. The best rank-$n$ approximation inequality gives $\sum_{i>n}\sigma_i^2\le D$. The sum of the largest $n$ singular values is at most $2p+\sqrt{nD}$, by the triangle inequality for the Ky Fan $n$-norm, Cauchy–Schwarz, and $G\succeq0$ with trace $2p$. Hence, by arithmetic–geometric mean,
\[
J:=\prod_{i=1}^r\sigma_i\ \le\
\left(\frac{2p+\sqrt{nD}}n\right)^n
\left(\frac D{r-n}\right)^{(r-n)/2}.
\]

## 3. Lower bound by counting column bases, without assuming $H\succeq0$

Write $H=V T V^T$ with $V$ of full column rank $r$ and $T$ diagonal of signature $\pm1$. For each column basis $I$ of $H$, the full minor on $I$ has determinant $\det(T)\det(V_I)^2$. Every nonzero principal minor of order $r$ occurs in this way, is an integer, and has the same sign. Their unsigned sum is $J$, by the characteristic coefficient. In particular $J$ is at least the number of column bases.

A $k$-dimensional span contains at most $m_k$ columns, where the following upper bounds suffice:
\[
(m_0,m_1,m_2,m_3,m_4,m_5)=(0,1,3,6,20,35).
\]
Indeed no column vanishes; diagonals 2 and other entries of magnitude at most 1 rule out parallel columns. For a set $F$ with column rank at most $k\le3$, its principal block has rank at most $k$. Every principal minor of order $\le3$ is nonnegative (at order three the determinant is $8-2(a^2+b^2+c^2)+2abc$, for $a,b,c\in\{0,\pm1\}$); bigger minors vanish. Thus the block is positive semidefinite. Its vectors, of norm squared 2, generate a positive definite integral lattice in their real span: in coordinates of a linearly independent subset, their coefficients are rational with bounded denominators by the integral Gram matrix. Its norm-two vectors form a finite simply laced root system under root reflections. The rank-two and rank-three ADE possibilities have at most 3 and 6 axes respectively.

For any $k$, a block of rank at most $k$ can be represented as $h_{ij}=v_i^T T'v_j$ in at most $k$ variables, allowing an indefinite signature. The matrix $(h_{ij}^3-h_{ij})$ is $6I$ on this block. It factors through homogeneous cubics in at most $k$ variables: use the polynomial
\[
(v^TT'w)^3-\tfrac14(v^TT'v)(w^TT'w)(v^TT'w)
\]
and $v_i^T T'v_i=2$. Thus the block size is at most $\binom{k+2}3$, giving the last two bounds.

Fix a column basis $B$ and take $d=p-r$ columns outside it. For every independent $k$-set $S$ outside $B$, extend it using $B$ alone to a basis whose outside part is exactly $S$. Different $S$ give different bases. When forming an ordered independent $k$-tuple of outside columns, at stage $j$ there are at least $\max(0,d-m_j)$ choices outside the span of the preceding columns. Therefore
\[
J\ \ge\ L(p,r):=1+\sum_{k=1}^{\min(r,6)}
   \frac1{k!}\prod_{j=0}^{k-1}\max(0,p-r-m_j).
\]

To compare the bounds, the verifier uses $\sqrt{nD}<s$ with $s=238/100$ or $297/100$. For every $13\le r\le26$ in dimension six and $14\le r\le53$ in dimension seven it checks exactly
\[
 L(p,r)^2>
  \left(\frac{2p+s}{n}\right)^{2n}
  \left(\frac{D_*}{r-n}\right)^{r-n}.
\]
This proves the rank claims. For scale, at the first excluded ranks the lower bounds are respectively 807 and 547,639; the corresponding singular-product upper bounds are below 492 and 536,086.

**Replay:** `node verify-kissing-frontier-angular-stability.js`. No dependencies beyond Node.js. The verifier checks both energy charts, the deficits, the integer angular counts, and every rank comparison.