# A uniform strict-pair cover for six-dimensional kissing configurations

**Theorem.** Every finite 60° spherical code in $\mathbb R^6$ can be partitioned into at most **40** parts, each a singleton or a pair at angle strictly greater than 120°. When the code has at most **74** points, **39** parts suffice. In particular, 73 points force **34 disjoint strict pairs**, and 74 force **35**. No symmetry, antipodes or prescribed subconfiguration is assumed.

These are structure bounds, not a determination of the kissing number; they neither construct nor exclude a 73–76 point code. The 72 roots of $E_6$ need at least 36 parts, so neither upper bound is asserted optimal. The earlier [size-specific results](KissingUnframedMatchings.md) gave 33 and 34 pairs at sizes 73 and 74, and 35 and 36 at sizes 75 and 76. We use [Tomar's cardinality bound of 76](https://www.mefyi.com/papers/kissing-numbers-five-seven/) for the original code **and** for the enlarged code described below.

## A charge for each component

Join $x,y$ when $x\cdot y<-1/2$ and let $\nu$ be the maximum matching size. The least number of parts is $L=N-\nu$. Let $T$ be a set of vertices maximizing $o(G-T)-|T|$ and, subject to this, maximizing $|T|$; $o$ counts odd components. By the Tutte–Berge formula, $N-2\nu=o(G-T)-|T|$.

Every component of $G-T$ is odd and factor-critical. Otherwise, in an even component remove one vertex, producing at least one odd component and enlarging $T$ without reducing the maximized difference. In an odd component $C$ that is not factor-critical, choose $v$ such that $C-v$ lacks a perfect matching. By Tutte's theorem and parity there is $S$ with $o(C-v-S)\ge |S|+2$. Adding $v$ and $S$ to $T$ again cannot reduce the difference. Finally, the graph is triangle-free by the squared norm of a sum of three unit vectors, and a three-vertex factor-critical graph would be a triangle. Thus the possible orders are $1,5,7,9,\ldots$.

Set $f(t)=t^4-t^2/4$. Its normalized dimension-six constant harmonic coefficient is $1/48$, with the other coefficients nonnegative. Between components $|x\cdot y|\le1/2$, hence $f(x\cdot y)\le0$. A component of order $k$ has charge $w_k$ if it supports a probability measure of $f$-energy at most $10^6/w_k$. Combining such measures with mass proportional to $w_k$ shows that any family of separated components must satisfy
\[
                         \sum_i w_{k_i}\le 48{,}000{,}000 .
\]
Indeed the combined energy is at most $10^6/\sum_i w_{k_i}$ and at least $1/48$.

Start with the [pinned seven-dimensional charges](https://github.com/mxym/math/blob/ebcb0c093d947093f246956f60d2e39a8f6697bd/research/euclidean-tensor-geometry/kissing-132-mixed-inputs.json); all apply in six dimensions by isometric embedding. We improve four orders by a direct dimension-six Bachoc–Vallentin three-point certificate. Here $U_k$ bounds $k$ times the $f$-energy of the **uniform** measure on any $k$ points. The improved charge is $\lfloor 10^6 k/U_k\rfloor$ (or its maximum with the inherited charge).

| $k$ | Exact upper bound $U_k$ | Bernstein cells visited |
|---:|---:|---:|
| 11 | $293113689489/195312500000$ | 2,063 |
| 27 | $81640028230243/50000000000000$ | 2,067 |
| 29 | $81956764716903/50000000000000$ | 9,655 |
| 31 | $164083463264557/100000000000000$ | 2,323 |

The positive factors, polynomial recurrence, and distinct-triple inequality are as in the [source-chart derivation](https://github.com/mxym/math/blob/ebcb0c093d947093f246956f60d2e39a8f6697bd/research/euclidean-tensor-geometry/KissingUniversalSixtyNineParts.md), with ambient dimension six in both zonal kernels. The check is on the continuous domain, not just sample points. For a cell crossing the Gram boundary $G(a,b,c)=1+2abc-a^2-b^2-c^2=0$, the new checker can certify its target $V\ge0$ on $G\ge0$ by finding $\lambda\ge0$ with $V-\lambda G\ge0$ on the entire cell. Both polynomials are expressed in the **same tensor Bernstein degree**. It subtracts $\lambda$ times upper-rounded coefficients for $G$ from lower-rounded coefficients for $V$. A proposed multiplier from floating-point ratios is used only after exact coefficient-by-coefficient testing, as a small integer times a power of two. Other branches either certify $V\ge0$ directly, exclude $G\ge0$ or the sorted order, or bisect outward. Dropping the Gram constraint can only enlarge the region to be proved.

## Exact integer accounting

Write $t=|T|$, $o=o(G-T)$, and let $s$ of the components be singletons. After deleting $T$, adjoin the negative of each surviving singleton. All new points are admissible: an old singleton has product in $[-1/2,1/2]$ with everything else, and its own opposite is new. Thus $N-t+s\le76$. We also have $2L=N-t+o$. These two counts are used separately; the initial $N$ can be smaller than the augmented count.

For each $(n,o,s)$ the verifier finds the smallest charge for odd components of total order $n$, with $o$ components and $s$ singletons. The initial state is $(0,0,0)$ of cost zero. Appending an allowed order $k$ increments the state by $(k,1,\mathbf1_{k=1})$ and costs $w_k$. The final sweep over $N,t$ tests $n=N-t$, $n+s\le76$, and $n+o\ge2L_0$. It need not assume that every counted multiset is geometrically realizable.

* For $N\le74$ and $L_0=40$, the minimum is **48,001,424**. It is attained by the counting relaxation at $N=74$ with sizes $(1,1,7,7,29,29)$.
* For $N\le76$ and $L_0=41$, it is **49,593,325**.

Both violate the 48-million budget. This proves the two claims, including for smaller codes that may not extend to a largest code. Whether 39 parts always suffice at sizes 75 and 76 is not settled here.

**Replay.** From this directory run **node verify-kissing-six-forty-parts.js** (standard Node; no dependencies). It checks the [four rational source rows](kissing-six-forty-component-charts.json) and the complete finite budget. Argument **budget** runs just the latter; integer size arguments run selected source charts.
