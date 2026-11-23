# Rank 36: excluding norm 24, unit norm 26 and type (1,21)

Of the twelve selected unit types, suppose precisely $(0,24),(0,26),(1,21)$ occur. This is one of the rank-36 alternatives left by the [three-type screen](panel-heights.md#all-rank-36-alternatives-with-exactly-three-selected-types). We will show that in this alternative the number $G_{1,21}$ of charge-one fields of squared norm 21 is at most 5,544 but at least 12,611.

## Fewer colorings per positive edge

We use the [positive-edge and wing description](affine-triples.md) for a field $b\in\{-1,0,1\}^{99}$ with $Ab=-4b-2{\bf1}$ and squared norm 21. It has a unique positive edge $pq$, and the common neighbor $h$ of $p,q$ is negative. The wings $X=N(p)\setminus\{q,h\}$ and $Y=N(q)\setminus\{p,h\}$ each have 12 vertices. Within each wing the induced edges form a perfect matching. The cross edges between wings form another perfect matching on their union. In each matching edge exactly one endpoint is negative and the other is zero. The 24 wing vertices are therefore partitioned into cycles alternating the internal and cross matchings. Cross edges switch wings, so the cycle lengths are divisible by four. Each cycle has two choices for which alternating class is negative. As proved in the positive-edge description, a fixed wing coloring extends to at most one field.

Let $b,b'$ be two fields with the same edge whose colorings differ on exactly two cycles of length four and agree everywhere else on the wings. Outside the wings and $\{p,q,h\}$, call the vertices far. Each field has three positive and three negative far vertices. A positive far vertex sees two negative vertices in each of $X,Y$: the common-neighbor slots of $p$ with the four other positive sites are already filled by its seven negative neighbors, and likewise for $q$. In the switched field $d_p+d_q-b$, where $d_i=3e_i-Ae_i$, the far signs are reversed and the negative and zero wing colors are interchanged. Thus a negative far vertex in $b'$ sees two **zero** vertices of $b'$ in each wing.

If a far site has opposite signs in $b,b'$, orient the pair so it is positive in $b$. The two common neighbors it has with each of $p,q$ must then be negative in $b$ and zero in $b'$. This requires four distinct neighbors among the negative corners of the two changed cycles. However, the two negative corners of any length-four cycle are nonadjacent (the negative set of $b$ is independent), and their other two corners are already both of their common neighbors. A far vertex can therefore see at most one negative corner in each such cycle. This contradiction rules out opposite far signs.

Now $b-b'$ is a nonzero integral $-4$ eigenvector, is unit, and has squared norm at most $8+12=20$. The minimum is 14, the norm is even (the signed sum is zero), and shells 16, 18 and 20 are absent: they are all unit and not among the three allowed types. So the norm is 14. The [Fano classification](../../short-support-packing/README.md#the-fano-configuration-is-determined-by-three-vertices-of-one-sign) says that two sites of one sign on this support already have both their common neighbors inside the support. But the exterior vertex $p$ sees two positive sites of $b-b'$: each changed four-cycle contributes one positive and one negative site in $X$. This contradiction proves that a pair of colorings differing in exactly two length-four cycles is impossible.

Let $k$ be the number of length-four cycles. After fixing the longer-cycle colors, the admissible $k$-bit colorings contain no pair at distance two. Here $k\in\{0,1,2,3,4,6\}$, and there are at most $\lfloor(6-k)/2\rfloor$ longer cycles. For $k=0,1,2,3,4,6$, the bit-code size is at most $1,2,2,2,4,8$, respectively. For $k\le3$, each parity class has at most one word; at $k=4$, two words in a parity class must be complements. At $k=6$ a parity class containing a complementary pair cannot contain a third word, since its distances to the pair would sum to six and each would have to be at least four. Otherwise all distinct words in that parity class are at distance four. Their real sign vectors then have squared length six and pairwise inner product $-2$, so $m$ such vectors have a sum of squared length $6m-2m(m-1)\ge0$, giving $m\le4$.

Multiplying the bit-code bound by $2^{\lfloor(6-k)/2\rfloor}$ gives at most eight fields per positive edge for all $k$. Consequently $G_{1,21}\le 8\cdot693=5,544$.

## The exact moment lower bound

The [second family bound](../short-shell-moments.md) is
\[
G_{0,20}+G_{1,21}+G_{1,27}+G_{2,30}\ \ge\ 21p/4,\qquad p=2402 .
\]
The counts $G_{0,20}$ and $G_{2,30}$ are unit-only, so they vanish. The [nonunit subtraction](../short-shell-moments.md#when-the-nonzero-labels-must-all-be-signed-units) gives $G_{1,27}=U_{1,27}+9G_{0,18}+2G_{2,26}$, where $U_{1,27}$ counts unit fields. Each summand vanishes, as $G_{0,18}$ and $G_{2,26}$ are unit-only. This yields $G_{1,21}\ge25,221/2$, hence at least 12,611 for the integer count. This contradicts the packing upper bound.

Together with the [earlier extra exclusion](affine-triples.md), at most eight of the 220 exactly-three-type alternatives remain at rank 36. This does not rule out rank 36.
