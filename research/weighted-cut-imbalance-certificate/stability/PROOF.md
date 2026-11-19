# Linear stability of the weighted cut–imbalance inequality

Let $w=(w_{ij})_{i<j}$ be the nonnegative edge weights of a finite loopless undirected graph, normalized by $\sum_{i<j}w_{ij}=1$. Aggregate parallel edges and freely adjoin isolated vertices. Write $d_i=\sum_{j\ne i}w_{ij}$, $c$ for the maximum cut weight, and
$$K(x)=\mathbb E\left|\sum_i x_i\epsilon_i\right|,\qquad B(c)=\frac{15c-6}{4},\qquad \delta=B(c)-K(d),$$
where the $\epsilon_i$ are independent uniform signs. The [weighted inequality](../PROOF.md) gives $\delta\ge0$. For a vertex set $S$ of size $r=3$ or $5$, let $u_S$ put weight $1/\binom r2$ on each pair in $S$ and zero on every other pair.

**Theorem.** After adjoining isolates if necessary,
$$\min_{S:\ |S|\in\{3,5\}}\ \sum_{i<j}|w_{ij}-(u_S)_{ij}|\le 40{,}000{,}000\,\delta.$$
The constant is independent of graph order and is not claimed optimal. The first power of $\delta$ cannot be replaced by $o(\delta)$. The distance counts all edges, including edges outside the chosen clique. This is graph stability, not stability of a coding protocol or a result on the separate BEKSZ degree-square conjecture.

## 1. Certificate information

Sort the actual degrees in nonincreasing order. Work in one common dimension, padding actual degrees and all comparison vectors by zeros up to at least 32. The [original certificate](../certificate.json) covers the parameter domain $1/2\le c\le2/3$ by closed convex polygons, partitioned into 957 leaves. Each leaf has fixed affine bounds for the prefix sums of sorted degrees. At its corners $z=(c_z,d_{\max,z})$ the certificate constructs comparison vectors $a^z$ of total 2. For an actual point in the leaf, choose a convex corner representation with weights $\theta_z$. By the original proof, $a=\sum_z\theta_z a^z$ majorizes $d$: its prefix sums dominate through rank 31 and are exactly 2 from rank 32 on, without any restriction on the number of actual nonzero degrees.

Every corner satisfies $K(a^z)\le B(c_z)$. A corner refers to its particular leaf and its bound choices, not to geometric coordinates alone. The [equality audit](../equality/PROOF.md) gives precisely three distinct possibilities at equality:
* $c_z=2/3$ and three coordinates of $2/3$;
* $c_z=3/5$ and five coordinates of $2/5$;
* $c_z=3/5$ and three coordinates of $107/260$ followed by two of $199/520$.

All unspecified coordinates vanish. On the first $r$ nonzero coordinates the signed sum's sign is the odd majority $M_r$, and its absolute value is at least $\beta=23/65$: the smallest majority-positive signed sum is $2-2\sum_{i\le(r-1)/2}a^z_i$. The five-coordinate witness with unequal entries need not correspond to an equality graph.

The two verifier replays additionally check:
1. In any leaf, all tight corners have the same $r$. There are 941 leaves with none, 10 with type 3 only, and 6 with type 5 only.
2. Every strict corner has $B(c_z)-K(a^z)\ge\eta$, where we may take $\eta=1/100000$.

For (2), writing $V=\sum_i(a_i^z)^2$ and $B=B(c_z)>0$, if $V<B^2$ then $K\le\sqrt V$ and $(B^2-V)/(2B)\le B-\sqrt V$. The [first verifier](verify_stability.py) uses this rational bound and otherwise computes $K$ exactly; its minimum certified slack is $2628961053934793912264210729/220968070077919745925211502873700>10^{-5}$. The [second verifier](independent_stability.py) instead tests $V\le(B-10^{-5})^2$ when $B>10^{-5}$, and computes exact sign sums in the remaining cases. It also reconstructs the dual bounds and polygon vertices by different methods. See the [receipts](INDEPENDENT-CHECKS.txt).

## 2. Almost all degree mass lies on three or five vertices

Let $h(\epsilon)=\operatorname{sgn}(d\cdot\epsilon)$, putting $h=0$ at ties, and $g_i=\mathbb E[\epsilon_i h]$. Then $K(d)=d\cdot g$ and $g$ is nonincreasing: for $i<j$, conditioning on the remaining signed sum $T$ gives
$$g_i-g_j=\tfrac12\mathbb E\big[\operatorname{sgn}(T+d_i-d_j)-\operatorname{sgn}(T-d_i+d_j)\big]\ge0.$$
Summation by parts thus gives $d\cdot g\le a\cdot g$. By affinity of $B$,
$$\delta=\sum_z\theta_z\big[B(c_z)-K(a^z)\big]+\sum_z\theta_z\big[K(a^z)-a^z\cdot g\big]+a\cdot g-d\cdot g.$$
All terms are nonnegative. The total weight $s$ of strict corners is at most $\delta/\eta$. Suppose $\delta<\eta/2$. The tight weights total at least $1/2$ and have a common type $r$ and cut coordinate $c_0$; consequently $E:=|c-c_0|\le s/6$ by the full width of $[1/2,2/3]$. At each tight corner the second loss inside the sum is $\mathbb E[|a^z\cdot\epsilon|\,|M_r-h|]$. Therefore $\mathbb E|M_r-h|\le2\delta/\beta$. The correlations of $M_r$ are constant $p_r=2^{1-r}\binom{r-1}{(r-1)/2}$ on the first $r$ coordinates and zero beyond them, so $p_3=1/2$ and $p_5=3/8$. Each differs from $g_i$ by at most $2\delta/\beta$. Since $\sum_i d_i=2$, we obtain, with $\tau=\sum_{i>r}d_i$,
$$p_r(2-\tau)\ge B(c)-\delta-4\delta/\beta
\ge B(c_0)-(1+4/\beta+5/(8\eta))\delta.$$
As $B(c_0)=2p_r$, the estimates (using $\beta>1/3$) give
$$E\le \tfrac{100000}{6}\delta,\qquad
\tau\le \tfrac83(1+12+62500)\delta. \tag{1}$$
If $\delta\ge\eta/2$ in this parameter domain, the trivial distance bound 2 gives the theorem with $L=4/\eta$.

For $c>2/3$, $K(d)\le1$: $(1,1,0,\ldots)$ majorizes the degrees, so this follows by the same sorted-sign argument. Hence $\delta\ge(15/4)(c-2/3)$. If $c>3/4$ then $\delta\ge5/16$ and the trivial bound suffices. Otherwise $b=(c,c,2-2c,0,\ldots)$ is sorted, sums to 2, and majorizes $d$ since each $d_i\le c$ by singleton cuts. Its sign is $M_3$, its margin is at least $1/2$, and $K(b)=1$. Now
$$\delta=(B(c)-1)+(1-b\cdot g)+(b\cdot g-d\cdot g).$$
The three terms are nonnegative, so $\mathbb E|h-M_3|\le2\delta$. It follows that $1-\delta\le K(d)\le(2-\tau)/2+4\delta$, hence $\tau\le10\delta$ and $E=c-2/3\le4\delta/15$ for $r=3$.

## 3. Recover the original edge weights

Total weight of outside-incident edges is at most $\tau$ (outside–outside edges are counted twice in the degree sum). For $r=3$, each top degree is at most $2/3+E$ and at least $2/3-\tau-2E$, since the three sum to $2-\tau$. Removing outside edges changes each degree by at most $\tau$. Thus each internal degree is within $2\tau+2E$ of $2/3$. In a triangle an edge weight is half the sum of the two endpoint degrees minus half the third degree. Each internal edge is within $3\tau+3E$ of $1/3$. Including exterior edges gives a distance at most $10\tau+9E$.

For $r=5$, let $q_{ij}=d_i+d_j-2w_{ij}$ be the cut isolating the pair $i,j$ within the whole graph, for $i,j\le5$. Its upper bound is $c\le3/5+E$. If $W_{\rm int}$ is the total edge weight on the first five vertices, the ten cuts sum to $4(2-\tau)-2W_{\rm int}\ge6-4\tau$. Thus each is at least $3/5-4\tau-9E$, and $|q_{ij}-3/5|\le A:=4\tau+9E$. For a fixed $i\le5$ let $e_i$ be its incident weight to outside, so $0\le e_i\le\tau$. Then
$$\sum_{j\ne i,\,j\le5}q_{ij}=d_i+2-\tau+2e_i.$$
It follows that $|d_i-2/5|\le4A+\tau$ and $|w_{ij}-1/10|\le9A/2+\tau$. The total distance is at most $45A+11\tau=191\tau+405E$. Substituting (1) gives a constant below $40{,}000{,}000$ for both clique sizes; all trivial and $c>2/3$ cases have smaller constants.

## 4. Sharpness of the power

On a triangle take edge weights $(1/3+t,1/3,1/3-t)$ for $0<t<1/12$. Then $c=2/3+t$ and its degree signs give strict three-bit majority, so $K(d)=1$. Consequently $\delta=15t/4$, while the distance to the on-support uniform triangle is $2t$. A different triangle has at most one of these edges; a uniform five-clique overlaps these edges in mass at most $3/10$. Their distances stay bounded away from zero as $t\downarrow0$. Thus no uniform $o(\delta)$ bound holds. This proves sharpness of the exponent only, not the optimal constant.
