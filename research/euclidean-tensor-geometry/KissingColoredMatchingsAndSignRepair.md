# Far-angle matchings, odd cycles, and sign repair in unrestricted kissing codes

In any **73-point** kissing code in six dimensions, **ten disjoint pairs** have inner product strictly below $-0.600$. In any **127-point** kissing code in seven dimensions, **eighteen disjoint pairs** do. At the wider cutoff $-0.550$ the guarantees are **19** and **28** pairs, respectively. At the usual $-1/2$ threshold, disjoint far pairs **and odd cycles together** cover all but at most three or five points, respectively. A maximum-cardinality code has such a cover with no omissions.

Every statement is conditional only on the dimension, cardinality and $60^\circ$ separation. No root frame, antipodality, harmonic vanishing, transitivity or integrality is assumed. We do **not** establish the existence of an excess code or improve either unrestricted cardinality bound.

## Ordinary matchings at stronger angles

Join distinct points in $G_a$ if their unit inner product is strictly less than $-a$. Entries are guaranteed matching sizes; different columns may be witnessed by different matchings.

| $a$ | .540 | .550 | .560 | .570 | .580 | .590 | .600 | .610 | .620 | .630 | .640 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $d=6,\ N=73$ | 22* | 19 | 18 | 16 | 15 | 12 | 10 | 8 | 7 | 6 | 4 |
| $d=7,\ N=127$ | 31 | 28 | 26 | 24 | 22 | 20 | 18 | 15 | 12 | 8 | 3 |

In six dimensions there are still **two** disjoint pairs at $a=.655$ and at least one at $a=.65921$. In seven dimensions at least one is forced at $a=.64406$. The starred entry comes from the [earlier barrier theorem](KissingUnframedMatchings.md), which gives the still stronger bounds 33 and 57 at the **different** threshold $a=.500$. For comparison, the old guarantees at $a=.550$ were 18 and 17, and at $a=.560$ were 15 and 7. These are improvements to certified guarantees, not assertions of sharpness. For $N_0+q$ points one may add $\lfloor q/2\rfloor$ to each matching guarantee in the corresponding $N_0$ row: repeatedly remove an edge while at least $N_0+2$ points remain and apply the bound again.

### The three color classes

No $G_a$ for $a\ge1/2$ has triangles, since the squared norm of three vertices in such a triangle would be negative. Suppose the largest matching has size $s\le m$ with $2m<N$. Its unmatched vertices are independent. Each matched edge has an endpoint with no unmatched neighbor: if both endpoints had such neighbors, these would either be distinct and give an augmenting path of length three, or be the same and give a triangle. Take one such free endpoint per edge. Thus there are three classes $U,V,W$ of sizes $N-2s,s,s$, with no $U$--$U$ or $U$--$V$ edge. To prescribe the sizes $N-2m,m,m$ instead, move $2(m-s)$ unmatched vertices in equal numbers from $U$ to $V$ and $W$. The two nonedge conditions remain valid; no edge between the moved vertices is required.

Write these final sizes $n_0,n_1,n_2$ and let $P_k$ be the normalized dimension-$d$ Gegenbauer polynomial. For any positive semidefinite matrices $C_k$ of order three put $F_{ij}(t)=\sum_{k\ge1}(C_k)_{ij}P_k(t)$. The addition formula, applied separately to each column of a square root of $C_k$, gives
$$
    0\le\sum_{x,y} F_{i(x),i(y)}(x\cdot y).
$$
For classes $(0,0),(0,1)$ all off-diagonal products belong to $[-a,1/2]$; for the others use $[-1,1/2]$. If $B_{ij}$ bounds $F_{ij}$ above on the appropriate interval, the right side is at most
$$
 \sum_i n_i F_{ii}(1)+
 \sum_{i\le j}(1+\mathbf1_{i\ne j})\,n_i(n_j-\mathbf1_{i=j}) B_{ij}.
$$
The [matrix certificate replay](verify-kissing-colored-matchings.py) makes this expression strictly **negative** at $m$ one less than every new multiedge entry stated above. Each $C_k$ is formed exactly as $AA^t/10^{12}$ from an integer matrix. The encoded arrays in the file expand to ordinary JSON integers. Bernstein subdivision with rational arithmetic bounds each univariate polynomial throughout the interval; the final assertion uses the exact rational bound, not its printed decimal. A sampled fit only supplied candidate factors.

## Forced odd cycles

The same code contains an **odd cycle** all of whose edges are strictly below $-a$ at each indicated threshold:

| dimension | size | $a$ |
|---|---:|---:|
| 6 | 73 or 74 | .50712 |
| 6 | 75 or 76 | .51373 |
| 7 | 127 or 128 | .50269 |
| 7 | 129 or 130 | .50531 |
| 7 | 131 or 132 | .50781 |

A bipartition would produce an independent class of at least $\lceil N/2\rceil$ vertices, hence a code with all off-diagonal products in $[-a,1/2]$. The same checker gives the respective independence upper bounds $36,37,63,64,65$. Each scalar certificate is $f=c_0+\sum c_k P_k$ with $c_0>0$, $c_k\ge0$, $f\le0$ on that closed interval, and $f(1)<c_0(B+1)$ for the specified bound $B$. Sum over all pairs to obtain the contradiction. Two more such scalar certificates give the single-edge assertions above. Every cycle in the table has length at least five; no common cycle at different thresholds is assumed.

## Exactly how many vertices must a pair-and-odd-cycle cover leave out?

For any $60^\circ$ code $X$ of size $N$ in dimension $d$, take $H=G_{1/2}$. A cover here means vertex-disjoint edges and odd cycles of $H$, not necessarily spanning. For an independent set $I$ delete its open neighborhood $N_H(I)$ and add the opposite of each vertex of $I$. This is a legal kissing code: each surviving old point off $I$ has absolute product at most $1/2$ with $I$, as do distinct elements of $I$. Any old opposite was in the deleted neighborhood and creates no duplication. The **maximum gain** of this simultaneous sign repair, including the empty repair, equals the **minimum number of uncovered vertices**:
$$
  \delta=\max_{I\ {\rm independent}}\bigl(|I|-|N_H(I)|\bigr)
       = N-\max_{\text{edge/odd-cycle covers}}|\text{covered vertices}|.
$$
For clarity the graph identity is classical perfect-2-matching theory; the sign-repair interpretation connects its deficit to kissing cardinality. Here is a proof. In the bipartite double cover, Hall's deficiency formula gives maximum matching size $N-\max_S(|S|-|N_H(S)|)$. It suffices to maximize over independent sets, since $I=S\setminus N_H(S)$ is independent and $N_H(I)\subseteq N_H(S)\setminus S$. A double-cover matching projects to vertex-disjoint directed paths and cycles. A path with $e$ edges has an alternating matching covering at least $e$ vertices. Replace an even cycle by alternating edges, interpret a two-cycle as a single edge, and keep each odd cycle. Thus at least the double-cover matching size in vertices is covered. Conversely every cover of $b$ vertices gives a double-cover matching of size $b$, by orienting odd cycles cyclically and using each single edge both ways.

In particular $\delta\le\tau_d-N$, where $\tau_d$ is the actual kissing number. By [Tomar's general bounds](https://www.mefyi.com/papers/kissing-numbers-five-seven/), at most $76-N$ or $132-N$ vertices need be omitted in dimensions six and seven. This is not an ordinary matching covering that many vertices: long odd cycles are allowed.

There is also a useful extremal reduction. Among maximum-cardinality codes take one with as many exact antipodal pairs as possible, and remove those pairs from its negative graph (each is an isolated edge). In the residual every nonempty independent $I$ has **strictly more** neighbors than vertices: a positive gain is impossible by maximality; at equality the sign repair preserves size and all old exact pairs, while creating $|I|$ new pairs. In each residual connected component every nonempty proper set $S$ consequently has $|N_H(S)|>|S|$; use the independent subset above when nonempty, or connectivity when $S\subseteq N_H(S)$. Each component has minimum degree at least two and is nonbipartite. Its two-copy bipartite graph still has a perfect matching after deleting **any one left vertex and any one right vertex**, by Hall. In particular deletion of any one original vertex leaves an edge/odd-cycle cover of all the other vertices of that component. The reduction is about an extremally chosen code, not an added assumption on every configuration.
