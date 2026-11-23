# The two binary octads and the 39-site zero layer

Work over F2 in the two adjacency eigencodes A x=εx, ε=0,1 (A²=A). If a nonzero binary word has support E of size s, let e be the number of edges induced by E and d_i the number of E-neighbors of i. Outside E all d_i are even, and within E their parity is ε. Counting neighbor pairs from E and then all outgoing edges gives

    s(s−1)−e−∑_(i∈E) C(d_i,2) = ∑_(i∉E) C(d_i,2) ≥ (14s−2e)/2.

In particular both binary codes have minimum weight at least eight. At weight eight equality throughout forces all outside degrees to be zero or two and all inside degrees at most one. For ε=1 the octad induces four disjoint edges, and for ε=0 it is independent. This argument makes no claim that either minimum is attained. These are binary adjacency code statements, not statements about the seven-ary self-orthogonal Seidel code.

Let U be the two-contact outside sites and V the zero-contact sites. Their sizes are (52,39) for a matching octad and (56,35) for an independent octad. Each pair of octad sites has exactly two labels in U unless it is a matched edge, which has one. For x in V, the two-walk count from x into E is 16. Thus x has eight U-neighbors and six in V. For y∈U the two-walk total into E is 14, with the two E-neighbors contributing 2ε; therefore it has 7−ε neighbors in U and 5+ε in V. The equitable quotient, in order E,U,V, is

    [[ε, 14−ε, 0],
     [2, 7−ε, 5+ε],
     [0, 8, 6]].

At every vertex in V its eight U labels are the edges of a simple two-factor on the eight points. Each point occurs twice by the diameter-two quota; no pair label repeats since the two U sites carrying that same pair already share both octad points and cannot share a V-site.

**Matching octad spectrum.** The ordinary real minus-four marking Gram restricted to E is 3I−M+J/9 for its matching M, with constant eigenvalue 26/9 and the other eigenvalues 2 and 4. Every pairing between E and V is 1/9. Consequently projecting the 39 V marks off these eight nondegenerate marks gives Gram
     
     3I−A_V+J/13.

Its constant vector is zero. On the orthogonal complement of the constants it is exactly 3I−A_V. Hence A_V, a six-regular graph, has real eigenvalue 3 with multiplicity at least 2. The preceding calculation also applies modulo seven, where 26,13 and 39 are units. If the full Seidel rank is r, then dim ker_F7(3I−A_V)≥46−r. The constant does not contribute to this stated kernel. The four rank cases give 10,8,6,4.

**Application to an invisible ten-cycle.** In [the elementary cycle theorem](saturated-elementary-five-cycle.md) the eight far extrema E give precisely such a matching octad for the full graph: Az=z+2h with z extended by zero off the far vertices. In U the 20 cycle dart sites represent all same-sign labels; the four shared off-cycle contacts and 28 other far neighbors supply the 32 cross-sign labels. The roots of T belong to V. The root for the physical wing carrying four cycle edges sees a C4 on each sign of the octad: there are four forward dart labels in that color, two at each of the four positive sites, and no parallel labels there since a same-wing pair has at most one far common site. For each of the wings carrying three edges, the three forward labels form a path of length three on the four positive sites, with degree sequence 1,1,2,2; the same holds negatively. Its two remaining labels are cross-sign and must connect the endpoints of the two paths, giving a single C8. These are necessary local shapes only.

For each of the three unordered balanced splits of the four matching edges into two sets of two, put v=±1 on E accordingly and 0 elsewhere. All entries of (3I−A)v/2 are integral: inside E the sign is constant along matching edges; any outsiders see zero or two octad sites. The resulting vector is neutral of graph norm 28 since v is centered, v^tAv=8 and (3I−A)^2=7(3I−A) on centered vectors. The three such unoriented norm-28 directions are pairwise orthogonal (use their three orthogonal sign vectors on the four edges). They consist of four units per sign on the octad and ten per sign among the 52 pair labels. This makes six distinct oriented norm-28 graph vectors per matching octad; no disjointness across different octads is asserted.

**Next weight.** The [binary nine-support theorem](binary-nine-support.md) classifies the two possible induced shapes and the contact-layer degrees. This is conditional on a binary kernel word of weight nine, whose existence is not forced.
