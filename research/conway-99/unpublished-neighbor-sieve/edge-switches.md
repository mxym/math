# Edge and triangle counts in the rank-36 witness

Use the [affine counting identity](affine-witness.md) and its notation. For a support $S$ of a norm-24 eigenvector let $j(S)$ count the edges joining equal signs whose triangle has third vertex outside $S$. Reversing all signs preserves this count. Let $\mathcal S$ denote the unoriented norm-24 supports. At rank 36 the sharper necessary condition is
$$
\sum_{S\in\mathcal S}\left(2-\frac{j(S)}2\right)+2F_1+F_2
\ \ge\ 124516+21N_{14}+2N_{18}.
$$
In particular at least 62,258 distinct vertex sets are still required if every norm-24 support with $j(S)\ge4$ is discarded. The count includes the two affine types of sizes 25 and 28. The [unsigned support uniqueness argument](norm16-packing.md) applies. Writing $F_{2,0}$ for the three-positive labelings with independent positives and $E_{20}$ for the number of twenty-site supports with a same-sign edge, the edge bijection below gives $F_2=F_{2,0}+2E_{20}$. Thus the same numerical lower bound holds on the number of distinct subsets of sizes 20, 24, 25 and 28 when the 24-site sets are restricted to $j(S)\le3$ and the 28-site sets to independent positives. The 20-site sets have 132 local shapes up to sign reversal.

## Counting the triangles without double counting their images

Put $d_i=3e_i-Ae_i$. For a triangle $T$, $D_T=\sum_{i\in T}d_i$ takes value one on its three sites, minus one on its 36 distinct external neighbors, and zero elsewhere. For a charge-$a$ solution $b$ one has
$$
\|D_T-b\|^2=39+\|b\|^2-14\sum_{i\in T}b_i-12a .
$$
The charge changes to $3-a$. For an oriented norm-24 vector $t$, a triangle with two positive sites and its third site unmarked therefore gives a solution $b=D_T-t$ counted by $G_{3,35}$.

Every such $b$ has one positive unit, 34 negative units and zeros elsewhere. In fact $\sum b_i=-33$ and $\sum b_i(b_i+1)=2$. The only other profile would have a single entry $-2$ and no positive entries. That site would need neighbor sum two, which is impossible. The positive site $z$ has ten negative and four unmarked neighbors. For fixed $b$, the triangles that give back a norm-24 vector are exactly its triangles with sum one. These consist of $z$ and a mate pair of its unmarked neighbors. Conversely for each such triangle the inverse vector $D_T-b$ has charge zero and squared norm 24, with positive endpoints at the two unmarked neighbors and zero at $z$. Thus the number of preimages is exactly the number of mate pairs among the four unmarked neighbors, between zero and two.

Summing over both orientations gives $\sum_{S\in\mathcal S}j(S)\le2G_{3,35}$. Each norm-24 support gives exactly two orientations. Retaining the $G_{3,35}$ term when using the [norm-sixteen bound](norm16-packing.md) in the affine identity proves the inequality.

## The same-sign edges are matchings

For both the norm-24 and the seven-positive $F_1$ labelings the positive side induces a matching together with isolated sites. Suppose a positive $p$ has distinct positive neighbors $q,r$. In the norm-24 case $p$ sees at least six negatives, and each of $q,r$ sees at least five. At most one of the latter lies among the negative neighbors of $p$ for each of $q,r$, since both are adjacent to $p$. The two sets of at least four negatives outside that neighborhood must intersect in at least two among at most six sites. The common positive neighbor $p$ would be a third common neighbor of $q,r$. At $F_1$ the respective numbers are eight, seven, six and ten. The same contradiction follows. Reversing signs proves the norm-24 assertion on the negative side as well.

An $F_1$ labeling with two positive edges has four distinct endpoints. They send 28 incidences into the eighteen negative sites. Each site receiving $h$ contributes $\binom h2\ge h-1$ positive pairs. The pair capacity of the endpoints is ten, since two pairs are adjacent and four are nonadjacent. Thus equality holds. Every negative receives one or two incidences, and every common neighbor of any two endpoints is negative. The ten double sites are recovered from the four endpoints. Each endpoint has two further single negative neighbors, and the other three positive sites miss all endpoints.

## Switching a positive edge of a three-positive labeling

Let $e=pq$ be the positive edge of an $F_2$ labeling $b$ and put $D_e=d_p+d_q$. Then $t=D_e-b$ is an integral $-4$ eigenvector of squared norm 20 with $t_p=t_q=1$. Indeed $D_e^2=36$ and $(D_e,b)=7(b_p+b_q)+4a$, with $a=2$. Conversely, a norm-20 vector having a positive edge $e$ gives a charge-two vector $b=D_e-t$ of squared norm 28. All such vectors have the $F_2$ unit profile by the [short affine profile argument](affine-witness.md).

To see that these maps are inverse bijections without a choice of edge, a norm-20 vector has ten positive and ten negative units by the same short-vector bound. Each side has the same number $e'$ of edges. On either side write $d(x)$ for the internal degree, and on the 79 outside sites let $k_x$ be the number of neighbors of each sign. For general equal side size $n$, counting the common neighbors of positive pairs and then using $\sum_{x\text{ outside}}k_x=10n-4e'$ gives
$$5e'+\sum_{x\text{ marked}}\binom{d(x)}2+
\sum_{x\text{ outside}}\frac{(k_x-1)(k_x-2)}2
= n^2-19n+99.$$
At $n=10$ the right side is nine, so each sign has at most one edge. The $F_2$ side also has at most one positive edge by the [three-positive classification](signed-supports.md). Hence the number of positive-edge $F_2$ labelings equals the number of oriented norm-20 vectors with an edge. Reversing $t$ pairs those labelings without a fixed point. Two norm-20 vectors on the same support agree up to sign, because their integral half-sum and half-difference have squared norms adding to twenty, below twice the minimum fourteen.

In the norm-20 representation the five negative neighbors of $p$ and the five of $q$ intersect in exactly one site $x$. Their intersection has size at most one. If it were empty the common neighbor of $p,q$ would have $t$-value zero (there is only one positive edge), giving $b$-value $-2$ there. Write $r$ for the unique negative missing both $p,q$. Any other positive seeing $x$ must see $r$. Its four negative neighbors can meet each five-set in at most two, and $x$ was counted twice. There are at least two such positives, so $x$ has exactly four positive neighbors: otherwise $x,r$ would have at least three common neighbors. Consequently $x$ is outside the negative edge. Interchanging the signs gives a positive site $w$ on the triangle of the negative edge, outside the positive edge.

The edges on the two signs are joined by a matching of size one or two. No endpoint sees both opposite endpoints, by the preceding result on $x,w$. At most one negative vertex misses both positive endpoints, so at least one cross edge exists. If there are two, the four endpoints form an induced square. In the one-cross-edge case $r$ belongs to the negative edge. In the two-cross-edge case $r$ is outside that edge. In the original $F_2$ representation the positives are $p,q,r$. The total marked common neighbors for the pairs $pr,qr$ is three in the first case and four in the second: among the four common-neighbor incidences, the unmarked ones are exactly the neighbors of $r$ in the negative wing vertices of $t$ at $p,q$, i.e. its internal degree in the negative side. Thus the two cases correspond to the last two rows of the three-positive census.

## Enumerating the signed twenty-site graphs

The ten-by-ten incidence matrix from positive to negative sites has row and column sums five at the two edge endpoints and four elsewhere. Each pair of rows or columns meets in at most two, and the two edge endpoints meet in one. Name the four endpoints first, with cross edges $p_0n_0$ and, in the two-match case, $p_1n_1$. On each side the bit masks of adjacency to the two opposite endpoints have populations one for both, four for each singleton, and one for neither.

Enumerate the eight remaining rows using these types and the sums. Within each identical type keep the rows in nondecreasing numerical order. Among columns of the same type and identical previously assigned prefix, put a new one-bit in the lower-index column first. These restrictions retain a representative: a lexicographically minimal sequence of numerical row masks among the admissible relabelings obeys both, since moving a one to a lower bit first decreases the first affected row. The first two rows and columns stay fixed. Check both common-neighbor bounds at every step. At the end use color-preserving graph isomorphism on the two sign sides, allowing all compatible endpoint permutations. This gives the following distinct signed graphs; each still has to extend to 99 vertices.

| Cross edges between the two internal edges | $x,w$ nonadjacent | $x,w$ adjacent |
| ---: | ---: | ---: |
| 1 | 40 | 48 |
| 2 | 71 | 23 |

Run `python3 edge_switch.py` with `pynauty` installed. The checker counts 168 and 242 row arrays before the final isomorphism check, verifies every same-sign and opposite-sign common-neighbor cap and reproduces the 182 shapes. Allowing a simultaneous exchange of the two signs gives counts 30, 32, 50 and 20 in row-major order, hence 132 shapes. The multiplicity of a shape on a fixed graph still needs to be bounded.

[Exterior height bounds for the norm-twenty fields](n20-exterior-heights.md) apply to both edge-bearing and independent sign sides and give an injective charge-two transform in the height-four case.
