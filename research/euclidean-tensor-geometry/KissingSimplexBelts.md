# Kissing codes in the common belts of a regular simplex

Let $C\subset S^{d-1}$ have pairwise inner products at most $1/2$, and let $v_1,\ldots,v_{d+1}$ be any regular unit simplex. Define the common belts
\[
 B_d(h)=\{x\in S^{d-1}: |x\cdot v_i|\le h\text{ for every }i\}.
\]
The frame is arbitrary; it need not be a subset of $C$ or generate any symmetry of $C$.

**Results.** In dimension five the maximum of $|C\cap B_5(h)|$ is **zero** for $0\le h<1/\sqrt5$, **20** for $1/\sqrt5\le h<\sqrt{3/10}$, and **30** at $h=\sqrt{3/10}$. All maximizers at that transition come from one-factorizations of $K_6$ in simplex coordinates. In dimensions six and seven we prove the following upper bounds:
\[
 |C\cap B_6(4097/8192)|\le58,\qquad
 |C\cap B_7(4097/8192)|\le114.
\]
The last two are bounds, not claimed optima. The cosine threshold is slightly larger than $1/2$.

**Consequences for extensions.** If $C$ contains every simplex vertex **and its antipode**, each other point lies in $B_d(1/2)$. The largest such five-dimensional configuration has exactly **32** points; the six- and seven-dimensional totals are at most **72** and **130**, respectively. In particular a hypothetical 73-point code in six dimensions cannot contain this 14-point frame. More robustly, the conclusion still holds when the distinct designated frame points are within Euclidean distance $1/8192$ of the corresponding signed simplex vertices: the other points satisfy the expanded belt inequalities by Cauchy–Schwarz. This is a structural obstruction, **not a determination of the unrestricted kissing numbers**. Compare the different [irreducible-symmetry theorem](KissingSevenIrreducible.md).

## 1. The exact five-dimensional transition

Use simplex coordinates $y\in\mathbb R^6$, $\sum y_i=0,\ \sum y_i^2=1$, with $x\cdot v_i=\sqrt{6/5}\,y_i$. Since $\tfrac16\sum_i(x\cdot v_i)^2=1/5$, the first range is empty. Put $r_i=2y_i$. Up to and including the transition, $|r_i|\le1$, $\sum r_i=0$ and $\sum r_i^2=4$. Write $s=\sum_{r_i>0}r_i=\tfrac12\sum |r_i|$. If there are at most two positive entries then $4=\sum r_i^2\le2s\le4$ forces exactly two $+1$, two $-1$ and two zeros. The same holds for at most two negatives. Every other vector has exactly three positive and three negative entries.

For two points whose signs fit the same balanced three-plus/three-minus pattern (zeros may be assigned either sign), let their magnitudes in the $r$-scale be $a_i,b_i$. Then
\[
 4\,y\cdot y'=\sum_i a_ib_i\ \ge\ \sum_i(a_i+b_i-1)\ \ge\ 4+4-6=2.
\]
The last inequality is strict if either point is not of the discrete $2(+1),2(-1),2(0)$ form, because $\sum a_i>\sum a_i^2$ then. Below the transition no discrete point is present, and at most one point can occupy each of the $\binom63=20$ patterns. All 20 balanced signs divided by $\sqrt6$ in the $y$-coordinates attain the bound, starting at $h=1/\sqrt5$; distinct vectors have dot product at most $1/3$. These twenty and the twelve frame points themselves give the claimed 32-point kissing code at $h=1/2$.

At the transition a discrete point belongs to two balanced patterns (assign its two zeros opposite signs), whereas a nondiscrete one belongs to just one and excludes every other point there. In one pattern two compatible discrete points must have disjoint pairs of zero positions: their scalar product is their common support size divided by four. Consequently there are at most three discrete points per pattern. With $u$ nondiscrete and $v$ discrete points, $3u+2v\le 3\binom63=60$. Hence $u+v\le30$, with equality only when $u=0$.

Write a discrete point as $(1_P-1_N)/2$ in the $y$-coordinates for disjoint two-element sets $P,N$. For fixed $P$, at most two negative pairs can occur and, if two occur, they are disjoint (sharing a coordinate gives scalar product $3/4$). The same goes for fixed $N$. At size 30 each of the fifteen edges occurs exactly twice in each role. If $P$ points to negative pairs $N,Q$, the three edges partition the six vertices. Because $N$ has two disjoint incoming edges, $Q$ must point to $N$ and hence also to $P$. Applying that incoming constraint to $P$ gives $N\to P$ and $N\to Q$. Thus the complete directed triangles of edges form a partition of all edges into perfect matchings, a one-factorization. Conversely, from any one-factorization take all six ordered pairs of distinct edges in each of its five matchings. Two distinct sign vectors would need at least three sign agreements to give dot product above $1/2$; that requires identical $P$ or identical $N$ with a non-disjoint other edge, which cannot occur. A one-factorization exists explicitly on $\{\infty\}\cup\mathbb Z_5$: matching $j$ consists of $(\infty,j),(j-1,j+1),(j-2,j+2)$.

## 2. Positive kernels for dimensions six and seven

Put $n=d+1$. Realize the unit sphere in $\sum y_i=0\subset\mathbb R^n$ with $v_i=(e_i-\mathbf1/n)/\sqrt{1-1/n}$. Now write $r_i=2(x\cdot v_i)=2\sqrt{n/d}\,y_i$, so $\sum r_i=0$, $\sum r_i^2=4n/d$ and $|r_i|\le4097/4096$. We exclude an $M$-point code entirely inside these belts, where $(d,M)=(6,59)$ or $(7,115)$. Any larger population would contain an $M$-point subset.

Use normalized Gegenbauer kernels $P_k$ in dimension $d$, with $(k+d-2)P_{k+1}=(2k+d-2)tP_k-kP_{k-1}$, $P_0=1,P_1=t$. Their positive semidefiniteness is the spherical addition formula; see [Delsarte–Goethals–Seidel](https://research.tue.nl/en/publications/spherical-codes-and-designs/). The [standard-library rational checker](verify-kissing-simplex-belts.py) supplies explicit positive coefficients $\alpha_k$ such that $f=\sum\alpha_kP_k\le0$ on $[-1,1/2]$. It proves this univariate sign by exact Bernstein subdivision (13 and 21 nodes). Only degrees $0,1,2,3,4,5,6,9,10$ occur.

Take reference orbits $O_j$ of the coordinate permutation group: all normalized centered indicators of $j$-subsets, $1\le j\le\lfloor n/2\rfloor$, followed by all roots $(e_i-e_h)/\sqrt2$, $i\ne h$. For $k=4,6$ define $(m_k(x))_j=\operatorname{avg}_{v\in O_j}P_k(x\cdot v)$ and $(C_k)_{ij}=\operatorname{avg}_{v\in O_i,w\in O_j}P_k(v\cdot w)$. Distinct rational reference weights $\beta_k$ are used at the two degrees. Positivity on the signed measure obtained by subtracting the reference measures with these weights from the uniform measure on a putative $M$-point code $Y$ yields
\[
 M^{-2}\sum_{x,y\in Y}P_k(x\cdot y)
 \ \ge\ 2\operatorname{avg}_{x\in Y}\beta_k^\top m_k(x)-\beta_k^\top C_k\beta_k.
\]
Other positive degrees give a nonnegative sum. Off the diagonal, $f\le0$. Thus the following function **cannot** be strictly positive at every point of $Y$:
\[
 L(x)=\alpha_0-\frac{f(1)}M+
 \sum_{k=4,6}\alpha_k(2\beta_k^\top m_k(x)-\beta_k^\top C_k\beta_k).
\]
This use of permutation-invariant reference measures imposes **no** permutation invariance on $Y$.

Let $p_j=\sum_i r_i^j$. A symmetric even polynomial of degree at most six, on $p_1=0$ and constant $p_2=4n/d$, is in the span of $1,p_4,p_6,p_3^2$ by the fundamental theorem of symmetric polynomials. The reference averages have exactly this property. The checker evaluates them at four centered normalized test vectors with rational squared normalization, solves the nonsingular four-by-four system in rationals, and cross-checks on five others. The four evaluations suffice by the dimension argument; the extra ones are redundant. Since all four basis functions are nonnegative, rounding each coefficient of $10^5 L$ down yields these lower bounds:
\[
\begin{array}{c|rrrr}
d&1&p_4&p_6&p_3^2\\ \hline
6&184231&-49652&6414&-1686\\
7&117587&-29633&1739&-363
\end{array}
\]

## 3. A short continuous-domain certificate

Here is how the checker proves the two rounded polynomials positive throughout the actual domain. Sort magnitudes separately by sign. Simultaneous negation preserves the lower polynomial, so enumerate positive-slot counts $p=\lceil n/2\rceil,\ldots,n-1$; zero coordinates can be assigned signs. Let $S=4096$ (or 3584 for the second replay). Cover every magnitude by an interval in units $1/S$, starting from $[0,(S+1)/S]$. Both grids contain the stated belt. Contract by sorting, signed sum zero, and the exact sum of squares.

For coefficients $(A,b,c,e)$ in the table, $b<0,c>0,e<0$. Write $z_i=r_i^2$. The function $bz_i^2+cz_i^3$ is concave over every outward-rounded square interval used. Lower-bound it there by its secant. The total $\sum z_i$ is fixed, so minimize the sum of secants by allocating any mass beyond the lower endpoints first to intervals in increasing slope order. The checker rounds base values and slopes downward. For the term with coefficient $e$ it bounds $|\sum r_i^3|$ from above, using each identity $\sum r_i^3=\sum(r_i^3-\tfrac j2r_i)$ for $j=0,\ldots,5$. In each magnitude interval the cubic $2s^3-js$ is convex; its upper bound comes from the endpoints and a lower tangent bound covers a possible interior minimum. Intersect these bounds and round outward. If positivity is not yet established, bisect the longest magnitude interval. No endpoint lattice restriction is imposed on the actual points.

| Dimension | grid $S=4096$, nodes / max depth | grid $S=3584$, reversed tie order |
|---|---:|---:|
| 6 | 539 / 33 | 521 / 22 |
| 7 | 1,264 / 35 | 1,202 / 29 |

Both runs use only integers and rational arithmetic, including the square roots rounded outward by integer square root. No open leaf remains. To reproduce both:

~~~sh
python3 verify-kissing-simplex-belts.py
~~~
