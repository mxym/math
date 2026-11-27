# A sharp threshold for antipodal chains in spherical kissing codes

In a set of unit vectors at mutual angles at least $60^\circ$, how long a chain can keep making nearly $180^\circ$ steps? The first nontrivial threshold is
\[
 a_*=0.862389331567416\ldots .
\]
In **every dimension**, join two points when their inner product is **strictly less** than $-a_*$. Every connected component is a path on **at most five vertices**. If equality is allowed instead, the bound is **ten vertices**. Both bounds are attained, in dimensions two and three respectively. The strict threshold cannot be decreased: one ten-point configuration in dimension three has all nine consecutive products exactly $-a_*$.

More precisely, maximize the least of $-\langle x_i,x_{i+1}\rangle$ along a path of $m$ edges and $m+1$ distinct kissing points, allowing arbitrary dimension. Then the optimum for $m=1$ is $1$, for $2\le m\le4$ it is $\sqrt3/2$, and for $5\le m\le9$ it is $a_*$. For $m\ge10$ it is strictly smaller than $a_*$ whenever such a path exists. This is a forbidden-subgraph result for the angular distribution; it does **not** determine either the six- or seven-dimensional kissing number.

## The extremizer

Let $u$ be the unique root in $(-.82,-.81)$ of
\[
              16u^4-16u^3-4u^2+10u-5=0 .
\]
The polynomial has opposite signs at the endpoints and negative derivative throughout. Write $b=1/[4(1-u^2)]$, $\theta=\arccos u$, and put
\[
 x_i=(\sqrt{1-b}\,(-1)^i,\sqrt b\cos(i\theta),\sqrt b\sin(i\theta)).
\]
The product at lag $j$ is $c_j=(1-b)(-1)^j+bT_j(u)$, where $T_j$ is the Chebyshev polynomial. In particular
\[
 c_1=-a_*=-1+\frac1{4(1-u)},\qquad c_2=c_5=\tfrac12 .
\]
The last equality also follows by factoring $1+T_5(u)-6(1-u^2)$ as $(u+1)(16u^4-16u^3-4u^2+10u-5)$. For reading, the remaining relevant products are

| Lag | 3 | 4 | 6 | 7 | 8 | 9 | 10 |
|---|---:|---:|---:|---:|---:|---:|---:|
| $c_j$ (approx.) | −.046 | −.334 | −.391 | .048 | .404 | −.800 | .993 |

Thus $x_0,\ldots,x_9$ are a kissing code, but appending $x_{10}$ fails. The [exact replay](verify-kissing-sharp-antipodal-path.py) checks every sign in the quartic quotient with rational isolating intervals.

## Why six points already force this value

Put $v=1-2u>2.6$. Let $R$ be the $6\times3$ matrix whose columns are the three successive zero-padded shifts of $(1,v,v,1)^t$. Set
\[
 H=\begin{pmatrix}v(v-1)&-v&1\\-v&v^2&-v\\1&-v&v(v-1)\end{pmatrix},
 \qquad Q=RHR^t .
\]
The leading principal minors of $H$ are $v(v-1)$, $v^2(v^2-v-1)$, and $v^2(v^2-v-1)^2$, all positive. Direct multiplication shows that an off-diagonal entry of $Q$ is positive at lags $1,2,5$ and zero at lags $3,4$. This is the entire dual certificate.

If $G_*$ is the Gram matrix of the six displayed vectors $x_0,\ldots,x_5$, then $R^tG_*=0$: the polynomial
\[
  1+vz+vz^2+z^3=(z+1)(z^2-2uz+1)
\]
annihilates each coordinate sequence. Consequently $\operatorname{tr}(QG_*)=0$. For any six distinct kissing points with Gram matrix $G$, the diagonal is unchanged and all products at lags $2,5$ are at most $1/2$, exactly their values in $G_*$. If all five successive products were below $-a_*$, the positive lag-one entries would give $\operatorname{tr}(QG)<0$. This contradicts $Q,G\succeq0$.

Moreover, if all consecutive products are merely **at most** $-a_*$, every lag $1,2,5$ product with positive dual weight must attain equality and $R^tG=0$. Indeed $\operatorname{tr}(H R^tGR)=0$ with $H\succ0$ forces $R^tGR=0$. The first three vectors now have fixed Gram matrix, and the rest satisfy
\[
 x_{j+3}=-x_j-vx_{j+1}-vx_{j+2}.
\]
This proves uniqueness of the ordered six-point extremizer up to isometry. Overlapping six-point windows propagate the same recurrence, so **every** such chain of at least six points is a segment of this three-dimensional one. An eleven-point chain is impossible by $c_{10}>1/2$. Compactness of the set of Gram matrices (unit diagonal, positive semidefinite, off-diagonal at most $1/2$) then makes the optimum strictly smaller for each fixed $m\ge10$.

For the shorter chain bound, the sum of two neighbors has norm at most $\sqrt3$, so the smaller of their negative products with the central vertex is at most $\sqrt3/2$. The five circle points at angles $150^\circ i$, $0\le i\le4$, attain equality on all four edges. A single pair of antipodes handles $m=1$.

## From chains to the whole graph

Three neighbors of one vertex have vector sum of norm at most $\sqrt6$. Since $3a_*>\sqrt6$, even the nonstrict graph has degree at most two. There are no cycles of length three or five: on an odd cycle of length $\ell$ the average consecutive product is at least $-\cos(\pi/\ell)$, by the eigenvalues of the cycle adjacency matrix applied to each coordinate. For a four-cycle the sum of its four edge products is $\langle x_0+x_2,x_1+x_3\rangle\ge-3$.

A strict cycle of length at least six would contain a forbidden six-point chain. In the nonstrict case a cycle longer than ten contains an eleven-point chain. On a cycle of length $6\le\ell\le10$ apply the recurrence on each successive window, **including** the window crossing the end: each such window consists of six distinct vertices. The sequence would return to its first point at lag $\ell$, whereas $c_\ell<1$ for every $\ell=6,\ldots,10$. This excludes the remaining cycles and proves both component bounds.

One useful counting consequence: on any $k$ vertices the strict graph has at most $k-\lceil k/5\rceil$ edges. This gives constraints on the number of very negative pairwise products that do not depend on the number of exact antipodal pairs, a root system, or even the ambient dimension.

**Reproduce:** run `python3 verify-kissing-sharp-antipodal-path.py`. The verification uses only the Python standard library, not an SDP solver. For the surrounding, different question of matching **existence** near the six-/seven-dimensional kissing frontier, see [the 21-point residual matching theorem](KissingFrontierNegativeMatching.md).
