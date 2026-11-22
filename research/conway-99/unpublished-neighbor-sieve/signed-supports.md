# Restricting the three support types at rank 36

The [affine counting identity](affine-witness.md) and [norm-sixteen packing bound](norm16-packing.md) require at least 62,258 distinct subsets from three types at rank 36. Write $P,N,Z$ for the positive, negative and unmarked sites of one labeling. The following restrictions on each type hold at every rank.

## Twelve positive and twelve negative sites

Let $t$ be an integral norm-24 eigenvector for $-4$. All entries belong to $\{0,1,-1\}$. Write $d_P(x),d_N(x)$ for the numbers of neighbors of $x$ in the two sign sets. Each sign set has the same number $e$ of internal edges, by counting the edges from $P$ to $N$ twice. Inside its own sign set let $d(x)$ denote the internal degree. On $Z$ put $k_z=d_P(z)=d_N(z)$. Then

$$
5e+\sum_{x\in P\cup N}\binom{d(x)}2
+\sum_{z\in Z}\frac{(k_z-1)(k_z-2)}2=15 .
$$

Indeed each opposite-side vertex $x\in N$ sees $4+d(x)$ positives. Counting pairs of positive neighbors over all 99 vertices gives $2\binom{12}2-e$. Subtracting the contributions in $P,N$ yields $\sum_{z\in Z}\binom{k_z}2=60-9e-\sum_x\binom{d(x)}2$, where the final sum is over the sign sets. The number of edges from $P$ to $Z$ is $120-4e$. Subtract it and add $|Z|=75$ to obtain the displayed identity.

Thus each sign has at most three internal edges. If it has three, these are disjoint on both sides. Exactly 33 unmarked vertices then see two sites of each sign, and the other 42 see one of each. For every $e$ there are at least $12-3e$ positive vertices with four negative neighbors chosen from four different matched pairs in their neighborhood. At most $2e$ positive sites lie on positive edges, and at most $e$ sites can be the common neighbor of the two endpoints of a negative edge.

**The twelve positive sites determine all twelve negative sites uniquely.** Fix $P$ and let $H$ consist of outside sites seeing at least four positives. All negatives belong to $H$. Each extra site costs at least three in the last sum of the identity, giving $|H|\le17$. Two distinct choices of twelve negatives in $H$ would have symmetric difference of size at most ten. The difference of the two labelings would be an integral $-4$ eigenvector with this squared norm, below the minimum fourteen. [Minimum norm bound](../short-support-packing/README.md)

## Seven positive and eighteen negative sites

For $Ab=-4b-2\mathbf1$, put $e=e(P)$. The negative side has $e+3$ internal edges. A negative vertex sees two more positives than negatives. Counting common neighbors of positive pairs gives
$$\sum_{z\in Z}\binom{d_P(z)}2+\sum_{x\in P\cup N}\binom{d(x)}2+5e=12.$$
In particular $e\le2$. Every positive edge belongs to a triangle with a negative third site. To see the last assertion, let $d_i=3e_i-Ae_i$ and for a triangle $T$ put $d_T=\sum_{i\in T}d_i$. This has value one on its three vertices and minus one on its 36 external neighbors, which are all distinct. For a charge-$a$ solution $b$, the vector $d_T-b$ has charge $3-a$ and squared norm $39+\|b\|^2-14\sum_{i\in T}b_i-12a$. With $a=1$, $\|b\|^2=25$ and triangle sum at least two this gives charge two and norm at most 24. Sum at least three gives norm ten, below the required absolute sum 22. Triangle sum two gives norm 24, already excluded in the affine counting proof.

**The seven positive sites determine all eighteen negative sites uniquely.** Let $H$ be the outside sites seeing at least two positives. It contains all eighteen negatives. Each extra site costs at least one in the first sum of the displayed identity, so $|H|\le30$. Suppose two choices of negative sites in $H$ are distinct. Write $K$ for their intersection and $U,V$ for their respective differences, of common size $s\le12$. Their signed difference is a nonzero integral $-4$ eigenvector, hence $s\ge7$.

The two difference sets have the same number $f$ of internal edges. On every site outside them put $k(x)=d_U(x)=d_V(x)$. As in the twelve-positive calculation, counting common neighbors of pairs in $U$ gives
$$\sum_{x\notin U\cup V}\binom{k(x)}2\le s(s-7)-9f.$$
Indeed each site of $V$ sees four more sites of $U$ than of $V$, contributing $6s+8f$ plus a nonnegative sum to the pair count. The sites of $U$ contribute another nonnegative sum.

Put $j=e(U,K)$ and $W=V(G)\setminus(P\cup K\cup U\cup V)$, so $|W|=74-s$. Each site in $U$ has two more positive neighbors than neighbors in $K\cup U$, giving $\sum_P k=2s+2f+j$. The number of edges from $U$ to $P\cup K\cup W$ is $10s-4f$, so $\sum_W k=8s-6f-2j$. Write $m(t)$ for the minimum of $\sum_{i=1}^7\binom{x_i}2$ over nonnegative integer $x_i$ of sum $t$. Balancing the entries attains this minimum. For $t\ge14$ each additional unit raises the minimum by at least two. Thus the pair count on $P$ is at least $m(2s)+4f+2j$. The pair count on $W$ is at least $\sum_W(k-1)=9s-74-6f-2j$. Together with the upper bound this requires
$$s(s-7)\ \ge\ m(2s)+9s-74+7f.$$
For $s=8,9,10,11,12$ the left sides are $8,18,30,44,60$ while the right sides at $f=0$ are $9,22,35,49,64$. At $s=7$ the upper bound on the entire pair count is zero, while the seven sites of $P$ alone contribute at least $m(14)=7$. This excludes every possible difference.

## Three positive and twenty-five negative sites

For $Ab=-4b-4\mathbf1$ each negative site has $d_N=d_P$, each zero has $d_N=4+d_P$, and each positive has $d_N=8+d_P$. Name the positives $0,1,2$. The class of any other site is the subset of these three that it sees. Let $s$ count sites seeing all three and let $h$ count the negative ones among them. The triple $u$ records the counts of negative sites seeing exactly pairs $01,02,12$ in that order. The names are chosen up to permutation and, for the single-edge case, $01$ is the edge. The column $k$ gives the number of negative sites seeing no positive. These $k$ sites have all fourteen neighbors unmarked.

The last two columns count the possible graphs induced on the 28 marked sites, with the three positive names fixed for each row and the negative names interchangeable. The same induced graph can occur in two different rows since $s$ counts unmarked sites as well. These are local candidates.

| Positive edges | $s$ | $h$ | $u$ | $k$ | After common-neighbor bounds | After both spectrum bounds |
|---:|---:|---:|:---:|---:|---:|---:|
| 0 | 0 | 0 | 0,1,2 | 4 | 736 | 318 |
| 0 | 0 | 0 | 0,2,2 | 5 | 1,087 | 613 |
| 0 | 0 | 0 | 1,1,1 | 4 | 1,878 | 1,240 |
| 0 | 0 | 0 | 1,1,2 | 5 | 2,944 | 2,276 |
| 0 | 0 | 0 | 1,2,2 | 6 | 4,541 | 4,068 |
| 0 | 0 | 0 | 2,2,2 | 7 | 6,858 | 5,508 |
| 0 | 1 | 1 | 0,0,0 | 3 | 34 | 15 |
| 0 | 1 | 1 | 0,0,1 | 4 | 72 | 47 |
| 0 | 1 | 1 | 0,1,1 | 5 | 190 | 163 |
| 0 | 1 | 0 | 1,1,1 | 4 | 1,878 | 1,240 |
| 0 | 1 | 1 | 1,1,1 | 6 | 566 | 566 |
| 1 | 0 | 0 | 1,1,2 | 3 | 123 | 99 |
| 1 | 0 | 0 | 1,2,2 | 4 | 78 | 76 |
| **Total** | | | | | **20,985** | **16,229** |

The positive sites together with the negative sites that see at least one positive uniquely determine the remaining $k$ negatives in the full graph. Indeed two completions could differ on at most $2k\le14$ sites. A nonzero difference would have to be a norm-14 Fano vector, with its two sides consisting of disjoint seven-sets. Every positive and every common visible negative misses both sides. In the Fano support, an outside vertex sees at most one site on each side because each pair on that side already has its two common neighbors inside. An outside vertex $x$ missing both sides has two common neighbors with each of the seven sites on one side. These fourteen neighbors of $x$ are all distinct and all see the support. Therefore two vertices missing the support cannot be adjacent. Here each positive is adjacent to at least eight visible negatives, giving a contradiction. [Fano support lemma](../rank-34-exclusion/README.md)

### Counting the classes

For positive adjacency masks $g_i$, two positives $i,j$ have $2-A_{ij}-|g_i\cap g_j|$ common neighbors outside the positives. Subtract $s$ to obtain the three double-class sizes. The degree 14 of each positive determines the single-class sizes, and the remaining sites form the empty class. Choosing the numbers of negative sites in the three double classes and the triple class determines the rest by the prescribed $8+d_P$ negative neighbors and the total of 25. There are 38 resulting signatures up to naming the positives.

Split each class by sign, giving cell sizes $m_j$, and keep the three positive singleton cells. For every site in cell $i$ enumerate its possible vectors of neighbor counts $r_j$ in the cells. Each vector has degree 14, the prescribed negative neighbor count, at most $m_j-\mathbf1_{i=j}$ entries in cell $j$, and the required common-neighbor counts with each positive. Twenty signatures have a nonempty cell without any possible vector.

For each of the other signatures let $n_{i,r}$ be the number of sites of cell $i$ with vector $r$. The population equation has right side $m_j$ and coefficient $\mathbf1_{i=j}$. The directed edge balance for cells $j,k$ has coefficient $\mathbf1_{i=j}r_k-\mathbf1_{i=k}r_j$ and right side zero. Finally, counting ordered paths of length two and directed edges between distinct endpoints in cells $j,k$ gives coefficient $r_j(r_k-\mathbf1_{j=k})+\mathbf1_{i=j}r_k$ and right side $2m_j(m_k-\mathbf1_{j=k})$. For five signatures the verifier supplies integer linear combinations of these equations with every coefficient nonnegative and the right side strictly negative. This gives the thirteen rows in the table. Run `python3 three_positive.py` to enumerate the neighbor vectors and check the five integer witnesses.

### Counting the induced graphs

The negative sites with no positive neighbor have degree zero in $N$. Those with one positive neighbor have degree one in $N$ and carry its name as a color. The remaining negative sites have their required degrees two or three. Enumerate the edges between these latter sites. For each outstanding incident edge assign a degree-one neighbor by its color. All unused degree-one sites pair off. The three counts of same-color pairs determine the three cross-color counts from the remaining populations. Permuting the degree-two and degree-three sites within each equal mask gives exactly the remaining labeling equivalence. The verifier keeps one representative and rejects any excess common neighbors among the 28 sites.

If $B$ is the adjacency matrix of these sites, the integer matrices $27I-9B+J$ and $44I+11B-2J$ must both be positive semidefinite. On the full graph these are 63 times the orthogonal projector onto the $-4$ eigenspace and 77 times the projector onto the $3$ eigenspace, respectively. Their principal submatrices inherit positivity. For a real symmetric matrix $K$ the coefficients of $\det(tI+K)$ are all nonnegative exactly when $K$ is positive semidefinite. A negative eigenvalue would give a positive real zero. Run `python3 three_positive_supports.py` with `python-flint` to construct the graphs and check all coefficients over the integers.

### Completing the neighborhoods of the positive edge

In each of the last two rows the positive edge is $01$. Each endpoint $p$ has one positive, nine negative and four unmarked neighbors. Completing each of these two lists individually reduces the 99 candidates in the penultimate row to seven and the 76 candidates in the final row to 22.

Let $R=12I+2J-B-B^2$. Its entry $R_{ij}$ is the number of unmarked common neighbors when $i\ne j$, and the unmarked degree when $i=j$. For each prospective unmarked neighbor $z$ of $p$, write $t$ for its binary vector of neighbors in the marked set. Its positive mask is $m$, so it has $4+|m|$ negative neighbors. Any two different selected sites $i,j$ must have $R_{ij}>0$. Also $(I+B)t\le2\mathbf1$, by counting common neighbors between $z$ and each marked site. The verifier enumerates the binary vectors satisfying these conditions.

The four chosen vectors sum to $R_{\cdot p}$, including its diagonal entry four. After deleting coordinate $p$, the target entries are zero, one or two. Encode the sum of two proposed vectors by the two disjoint masks for coordinates occurring once and twice. A lookup of the complementary masks generates every valid four-vector sum. Different chosen vectors can share at most one further site. Since the neighborhood of $p$ induces seven disjoint edges, a proposed site that already has its mate among the marked vertices has no mate left to choose. Pair off the remaining proposed sites, and test all common-neighbor bounds on the resulting 32 vertices. Applying this necessary test at both ends yields the counts above. The two neighborhoods still need to extend to the same graph. Run `python3 positive_edge.py` to check the two counts with integer arithmetic.

### Two further restrictions from unmarked vertices

For any positive $p$, let $D$ be its marked neighbors, $u=14-|D|$, and let $f$ count vertices of $D$ still missing their mate in the neighborhood of $p$. The $u$ unmarked neighbors must supply $f$ mates, with $(u-f)/2$ additional mate pairs among themselves. Every marked nonneighbor of $p$ sees a different nonmate pair among the fourteen neighbors of $p$. Thus at most $\binom u2-(u-f)/2$ such sites can miss all of $D$. For any $i\in D$, at most $u-\mathbf1_{i\text{ needs a mate}}$ can see $i$ alone in $D$.

For a nonempty subset of the positives, give its vertices weight $-2$, give weight one to each negative missing that subset, and give all other vertices weight zero. Write $v$ for the weights on the marked set. For each of the 71 unmarked vertices $z$, let $t_z$ be the sum of weights at its neighbors. From regularity and the common-neighbor counts,
$$\sum_z t_z=14\mathbf1^t v-\mathbf1^tBv,\qquad \sum_z t_z^2=v^t Rv.$$
If the first sum is $71a+b$ with $0\le b<71$, the second sum must be at least $(71-b)a^2+b(a+1)^2$. This follows by balancing 71 integers with fixed sum.

Checking these two restrictions at all three positives and all seven nonempty subsets leaves 13,606 of the 16,229 candidates in the table. Including the endpoint neighborhood test leaves **13,598** across all signatures, including **six and eighteen** in the last two rows. These **24** local possibilities cover the entire positive-edge case. Each count uses the same fixed positive names as the table. Both verifiers check the new restrictions in exact arithmetic.

### An upper bound of 11,125 using odd integers

Let $T$ be the hypothetical $28$ by $71$ incidence matrix from marked to unmarked sites, so $TT^t=R$ and $T\mathbf1=d$, the unmarked degree vector. For every integer $c$ that is odd and every integral column $v$ of length 28, all 71 entries of $c\mathbf1+2T^t v$ are odd. This gives the necessary inequality
$$71c^2+4c\,v^t d+4v^tRv\ \ge\ 71.$$
Every candidate rejected here has an explicit pair $(c,v)$ for which the integer left side is strictly smaller than 71.

To find such pairs, let $a$ have value $-1$ on the positives and $1$ on the negatives. The labeling equation gives $T^ta=4\mathbf1$. The left side is therefore $4(v+ca/8)^tR(v+ca/8)$. Changing $c$ by eight translates $v$ by an integer vector, and negation preserves the square. It suffices to consider $c=1,3$. The search uses the Gram matrix $500R+I$ to avoid dependence among the rows, with squared search radius 7,975 in that metric. The verifier tests each returned integer vector against the displayed inequality using the original $R$. A search that finds no witness retains the candidate.

The neighbor-pair capacities and the positive-edge neighborhood tests leave 13,647 candidates before either integer rounding test. Of these **2,522** have verified odd-vector obstructions, leaving **11,125**. In the row order of the table the remaining counts are $121,350,492,1699,3112,4227,8,42,119,492,439,6,18$. Run `python3 outside_squares.py` with `python-flint` and `fpylll` to regenerate and check the integer certificates. The search only provides an upper bound on the number of extendible candidates.
