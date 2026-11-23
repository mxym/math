# Exact complementary norm-16 partition by rook grids and original shadow marks

Let G be a hypothetical SRG(99,14,1,2). Throughout, N_t^+ counts actual oriented integral neutral +3 eigenvectors of ordinary squared norm t, and x_j^+ refers to the scaled complementary dual [rank-56 sector](../complementary-rank56/README.md). C_old(a,t) refers only to the original zero-seven-class old −4 label population, not to an extension or a complementary count.

Let D_8 count unordered anticomplete pairs of actual cubic eight-sets, and n_1 count unordered pairs of actual rook grids meeting in a single vertex. Define eligible original charge-one norm-37 buckets as follows: for every actual eight-set P of minimum degree at least three and thirteen edges, place P in its bucket b, the old integral evaluation of −w(1_P). Let m_b be the bucket size, with empty buckets omitted. Then

    N_16^+ = 2 D_8 + 2 n_1 + Σ_b m_b(m_b−1),
    x_8^+ = 2 D_8 + 2 n_1 + Σ_b m_b(m_b−1) + 2 F^+(2,18).

Every m_b≤4, and m_b≤3 when b has a coordinate +2. In particular the residual term Σ_b m_b(m_b−1) is at most 12 C_old(1,37). This is a literal partition and no population is assumed nonzero.

## Unit signs and the three possible cross-edge counts

With d_i^+=(A+4I)e_i, a negative entry at most −2 in a norm-16 field would give, after adding d_i^+, a charge-two field of norm at most 18. The mass is 18, so any such field would be a nonnegative unit indicator, but the double position becomes +2 if it was −2; a larger negative instead gives norm below 18. Apply also to the opposite sign. Thus every norm-16 field is unit.

Write its positive and negative sets as P,N, each of size eight. On each shore the same-sign degree is three plus the opposite-sign degree. An induced eight-set of minimum degree three has maximum degree four: if a vertex has D≥5 neighbours within the set, those neighbours induce a matching and require at least D total edges to the remaining 7−D sites, while each such site can account for at most two common neighbours with the root. This is impossible when D≥5. Thus the cross graph between P,N is a matching, with E edges, and 2e(P)=24+E=2e(N).

Put h=(A−3I)1_P=(A−3I)1_N, from the neutral equation. On the two sign shores h is one at each matching endpoint and zero elsewhere. On the 83 zero sites h is their common number r of P and N neighbours. The exact formulas are

    Ah=16·1−4h,   Σh=88,   Σh²=128−7E,
    Σ_zero r(r−1)=40−7E.

They follow from (A+4I)(A−3I)=2J and (A−3I)^2=−7(A−3I)+2J. Since E is even, these force E∈{0,2,4}. The E=0 fields are exactly the two orientations of every pair of anticomplete cubic eight-sets by the [centered Rayleigh characterization](normalized-cubic-shadow-classes.md).

## Exactly four cross-edges means a one-point grid difference

For E=4, each shore has fourteen internal edges, four degree-four high sites, and four degree-three low sites. Work within one shore and write H,L for its high and low parts. For a high vertex x the total common-neighbour slots with the other seven shore sites are 14−4=10. The contribution from shore neighbours is 8+d_H(x), so d_H(x)≤2. Degree sums give e(H)=e(L)+2. Hence e(H) is 2,3 or4.

* If e(H)=2, the lows are independent and each misses exactly one of the four highs. Two highs then have exactly 4−d_H(v)−d_H(w) common low neighbours. If H is a matching, endpoints of an edge have two common lows. If H is a length-two path and an isolate, a path endpoint and the isolate have three. Both violate the corresponding common-neighbour caps.
* If e(H)=3 and H is a triangle plus an isolate, the three high vertices on the triangle each need two low neighbours, and the three two-sets must be disjoint because those triangle edges already have their internal caps. This is impossible on four lows. Otherwise H is a path a−b−c−d. Endpoints a,d each miss exactly one low site, say α,δ. The pair a,b is adjacent and the pair a,c already shares b, so both b,c must include α in their two low neighbours (otherwise they share two lows with a). Symmetrically they must include δ. If α≠δ, b and c share two lows despite adjacency. If α=δ, a,d share three lows despite nonadjacency. Both fail.
* Therefore H is a four-cycle. Any low vertex hits at most two highs since an opposite high pair already has two common neighbours in the high cycle. It therefore has at least one low neighbour. As e(L)=2, the lows form a matching and each hits two highs.

For both shores, the high sites have used all their within-shore pair quotas, and each low site has precisely three remaining pair slots involving it (11 total, eight accounted for by three shore neighbours of degrees 4,4,3). Outside one shore a site cannot have precisely three contacts to it, because adjoining it would give a 17-edge nine-set, forbidden by the [nine-site density gap](../../conway-99-involution/grid-density-gap/README.md). It also cannot have five or more, by the 18-edge maximum on nine vertices. Thus r∈{0,1,2,4}. Since E=4, the height moment gives n_2+6n_4=6.

If n_4=1, its site adjoined to each shore gives an 18-edge nine-set, hence two rook grids with their sole common vertex at that site. Conversely two grids meeting in one point give such a field by subtraction of their charge-one indicators; the four neighbours of that point in either grid have internal degree three after deletion, while the four nonneighbours retain degree four and each has one cross contact by the one-domination property. The oriented difference recovers both shores and the sole height-four vertex, so this contributes exactly 2 n_1.

Otherwise there are six height-two sites and nine height-zero sites off the shores, all other zero sites having height one. The six height-two sites touch only low sign sites, since an additional common-neighbour witness with a high site would exceed its full shore-pair budget. Each low has exactly three height-two neighbours from its three remaining pair slots: another-sign site has at most one neighbour on that shore, a height-one site has at most one, and height four is absent. The unordered pairs of height-two sites already receive at least 8·choose(3,2)=24 common-neighbour incidences from the eight low sign sites. Each height-zero site off the shores sees no sign site and by Ah=16 needs at least two height-two neighbours among its fourteen neighbours, giving at least nine more incidences. But their total common-neighbour capacity is 2·choose(6,2)=30. This contradiction eliminates the no-height-four case.

## The two-cross branch is precisely the old charge-one norm-37 bucket count

An actual min-degree-three eight-set P with thirteen edges has two degree-four sites and six degree-three sites as above. Its original old mark w(−1_P) has squared norm 46/9 by Gram 3I−A+J/9, normalized charge +1 because −8≡1 mod9, and raw cost (7·46+11)/9=37. It is in the zero original seven-class since w(−1_P)−u_0 is a sum of differences and −9u_0. Its raw evaluation is b=h−1 for h=(A−3I)1_P. Exterior h≤3: four contacts produce a forbidden 17-edge nine-set, while five contacts would give a grid but P would then have fourteen edges, not thirteen; larger is impossible.

For two supports P,Q in one bucket, h_P=h_Q exactly. If they differ, the neutral unit field 1_P−1_Q has squared norm 16−2|P∩Q|, at least twelve by the [complementary minimum](../complementary-rank56/README.md). Thus the overlap I has size at most two. If I is nonempty, every exclusive P site touching I is one of P's two high sites, because at such a site h_Q counts contacts into Q and equals its one-or-zero in-shore height h_P; there are at most two edges from I to P∖Q. But each I site needs at least 4−|I| such neighbours by minimum degree three, contradiction. Thus different members of a bucket are disjoint, and their cross graph is exactly the two-edge matching given by their shared h=0/1 on both supports. Conversely every E=2 field comes from exactly such an oriented pair, recovering both supports from its signs.

For a bucket of m disjoint members, the common h has first moment 88 and second moment 114. On each selected support it takes value one at two sites and zero at six. For nonnegative integral h, 2·1_{h>0}≥3h−h², so the number of positive sites outside the m supports is at least [3(88−2m)−(114−2m)]/2=75−2m. There are only 99−8m sites outside, giving m≤4. If a height-three site occurs, the inequality is strict, excluding m=4. This proves the class cap and the exact two-cross term. The x_8^+ formula follows from the binary dual dictionary: the possible terms are neutral norm16 and norm-two, charge magnitude one norm13, and charge magnitude two norm18. The neutral norm-two term vanishes by the minimum twelve. At charge one and cost 13, the excess four is two entries of type +2 or −1. At most two negative units cannot obtain neighbour sum −2, so no negative is possible; then a double would require all fourteen neighbours nonzero despite total mass nine. Thus charge-one norm13 also vanishes.

## A second original-shell bound for the buckets with three-contact sites

Write j_b for the number of sites of h-height three in each nonempty eligible bucket. Then

    Σ_b choose(j_b,2) ≤ 15 [ C_old(1,23)−99 ].

Indeed let D_i=(3I−A)e_i, the old charge-one norm-23 mark. For a bucket label b of raw norm37, at two distinct positive-doubled sites i,j the field b−D_i−D_j has charge −1 and norm 23−14 A_ij, using b·D_i=7b_i+2 and D_i·D_j=2−7A_ij. Adjacency would give norm nine, below the absolute charge mass eleven. Thus i,j are nonadjacent and g=D_i+D_j−b is a true original charge-one norm-23 field, with value +1 at both i,j.

It cannot be a canonical D_k. If it were, equality of old marks would make 1_P+e_i+e_j−e_k a charge-one mass-nine +3 field. If k=i or j one instead gets b=D_j or D_i, impossible by its norm. If k is outside P and distinct from i,j, the lone negative cannot obtain neighbour sum −2. Thus k∈P, in which case the field is a nine-set indicator and hence a rook grid. Its edge count would be at most 13−3+3+3=16, because k had degree at least three, i,j originally had three contacts each to P, and i,j are nonadjacent. This is impossible. Therefore the image g is one of the extra original charge-one norm-23 marks. Such a g has at most six positions equal to +1 because squared norm 23 and mass −11 bound its total positive mass by six. There are at most 15 possible unordered pairs {i,j}, and each pair reconstructs its bucket label as b=D_i+D_j−g. This proves the bound with multiplicities and supplies a literal second old-shell coupling, without requiring any j_b>1.
