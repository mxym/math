# An independent, mandatory family of primal norm-eight vectors

This bound holds at every mod-seven Seidel rank, without a symmetry hypothesis. It is not a nonexistence result. The standalone checker verifies the local indexing and final arithmetic.

Under SRG(99,14,1,2), define C=3I−A+J/9, u_i its Gram vectors and w(c)=sum c_i u_i. Let M be the difference lattice and L=M+Z·3u_0. In L/M the coordinate sum of any input (divisible by 3) is determined modulo 9. Write y4 for the number of squared-norm-eight vectors in L, P for the number of induced triangular prisms, D0=floor(5P/2) and g=floor(P/6), where 0≤P≤851. Previous work: [counted marks and the balanced mass-six lemma](../rank-34-short-support/README.md); [nine-site classification](../../conway-99-involution/grid-density-gap/README.md). All marks below are genuine vectors of L, for every mod-seven rank.

**Claim.** Add the following new summand to the existing lower bound:
    
    y4 ≥ 1398474+765072+18P−48D0+2(831600+36P−2286g)
         +96(2079−9g)+103(8316−6P) ≥ 3564978.

It is 4882878 at P=0. This strengthens a coefficient inequality, not a rank exclusion.

The [triangle-pair packing bound](../rook-array-exclusion/triangle-pair-packing.md#consequences-for-the-short-lattice-shells) uses the actual number of grids and bounds equal-mark prism collisions. It raises the uniform lower bound for this shell to **3,724,902**.

## Eligible five-sets

Take F a bowtie (two triangles sharing one vertex), not contained in a nine-site rook grid, or take F an ordinary house. A house consists of a chordless square on vertices 0,1,2,3 in that cyclic order, and its cap 4 on edge 01, with no other edges. It is ordinary when the cap of opposite edge 23 is nonadjacent to 4. This excludes exactly the houses extendible to an induced triangular prism: in any completion the house's unique triangle is retained, and the unique 23 cap must be the added site. It sees neither 0 nor 1: otherwise it gives a third common neighbor to an opposite square pair, since vertex caps are outside the square. This applies to all four sides. There are 2079 squares (choose a nonedge, take its two nonadjacent common neighbors, divide by 2) and 4 distinct houses per square. A prism has six contained houses, and an extendible house has unique completion. Thus N_H=8316−6P exactly. In a nine-site rook grid every induced square is an axis rectangle and both opposite caps lie in the remaining common row or column and are adjacent. Hence every ordinary house is nongrid. Each vertex is in seven triangles, giving 99*C(7,2)=2079 bowties total, and each grid contains nine. Each grid contains 6 prisms, each prism uniquely extends to a grid if at all, so at most g grids. Thus at least 2079−9g eligible bowties.

Any vertex outside an eligible F sees at most two sites of F. For a bowtie, a neighbor of the center sees none of the leaves (the neighborhood is a matching); otherwise it can see at most one of each mated pair (its edge's unique common neighbor is the center). For a house, an outsider cannot meet opposite square vertices because their two common neighbors are already accounted for. Triple contact would have to use cap 4 and two adjacent square vertices. Touching 4 precludes 0 and 1 (cap-edge triangles already exhausted), so these must be 2,3. Then the outsider is the 23 cap, completing the prism.

## Counting anticomplete edges exactly up to a small correction

Let U consist of the outside vertices with no neighbors in F; D the outside vertices with two neighbors in F, and T those with one. The total number of edges from F to its exterior is 58. For each pair i<j in F, multiplicity in D as its F-neighbor set is 2−A_ij−|N_F(i)∩N_F(j)|, so |U|=36+|D| is 40 for bowties, 41 for houses. For x∈U its five nonadjacencies to F give exactly 10 two-step incidences, hence d_U(x)=4+d_D(x). For z∈D with F-neighbors i,j, there are exactly 8 two-step incidences to F. Of these d_i+d_j come through i,j (d_i denotes degree in F); the others come via T once or D twice. Therefore d_U(z)=4+d_i+d_j+d_D(z). Sum over U and count the U-to-D edges the other way to obtain:

    2e(U)=4|U|+Σ_{z∈D}(4+d_i+d_j)+2e(D).

The constant halves are B=96 (bowtie), B=103 (house), as checked by [the verifier](verify.py).

For every edge e in U, the mark c=1_F−1_e has two mutually anticomplete sign sides; its squared norm is 3(5+2)−2(6+1)+3²/9=8. Thus w(c) lies in L, with class +3 modulo 9.

## Exact control of repetitions within this family

For any occurring y=w(c), b=(3I−A)c is uniquely determined by y and the fixed sum 3: b_i=(u_i,y)−1/3. At the two endpoints of e it equals −2; on F it equals 3−d_i≥−1. All other b=−2 sites are in D and miss both endpoints of e. Consequently e is an isolated edge in the induced graph on {b=−2}; every alternative representing edge has both endpoints in D. If an alternative has the same e, the balanced difference of its five-sets has positive mass ≤5 and maps to zero, impossible by the established balanced mass-six lemma. So raw multiplicity m(F,e) is at most three from |{b=−2}|≤7. More exactly, for a bowtie only four D sites exist; for a house they have F-neighbor sets 12,03,23,42,43 in the labeling above. The 23 site has no neighbors elsewhere in D, since its triangle with 2 and 3 exhausts either cap-edge at any shared site. Thus there are at most four nonisolated D vertices in both cases.

If m(F,e)≤2 always for this fixed F, summing its shares 1/m gives at least B/2. Otherwise, the raw mark with multiplicity three has two other representing edges in D and both are isolated in the common {b=−2}. These account for all four possibly nonisolated D vertices, so D induces exactly two independent edges plus any isolated vertices. For an arbitrary e in U, define t_e as the number, out of these two D edges, with an endpoint adjacent to an endpoint of e. Those cannot represent y. Thus m(F,e)≤3−t_e, and for t_e=0,1,2 we have 1/m≥1/3+t_e/6.

For each of these D edges zz', both endpoints have exactly one D neighbor and at least 9 U neighbors by the displayed degree formula. Since zz' have at most one common neighbor, B'=U∩(N(z)∪N(z')) contains ≥17 vertices. Its induced graph has maximum degree two: the unique common cap has no neighbors in the two private wings; each private wing lies in a matching and a vertex of it has at most one neighbor in the opposite wing (the opposite center is a nonneighbor and its common neighbors already include the near center). Therefore e(B')≤|B'|. Since d_U≥4, at least 4|B'|−e(B')≥51 edges of U meet B'. Summing over the two D edges gives Σ_e t_e≥102. Now Σ_e 1/m≥(B+2)/3+17≥B/2 for both values B. Summing all F's shares counts every occurring y exactly once. Reversing all signs gives a disjoint set, hence at least the new summand stated above.

## Disjointness from all earlier marks

The earlier repository y4 count uses only (1,1),(2,2),(3,3), ±(3,0), ±(4,1), ±(6,0); in (a,b) each coordinate is respectively 1 or −1, and exactly a and b such coordinates occur. Among these only (3,0),(4,1),−(6,0) have the same sum modulo 9 as our new +3 marks. A collision with the first has balanced positive mass at most 5 and is impossible. A collision with (4,1) has balanced positive mass at most 6; if equality of images holds, the balanced mass-six lemma forces mass six, unit coefficients and two anticomplete induced prisms as signs. The positive sign set must then include all of F plus the previous lone negative (attaining the full mass six rules out cancellation). A prism minus one point is a prism-extendible house. Neither a bowtie nor an ordinary house can be such a set.

For the opposite-six old mark −1_X, setting h=1_F−1_e+1_X yields sum 9 and Ah=3h+1 in a collision. A negative site would require neighbor sum −2 with at most one other negative site, impossible. Thus h≥0, and e⊆X. A doubled site forces all 14 of its neighbors to be positive, since a zero site must have neighbor sum exactly 1. Contradicts total 9. So h is a unit indicator, contains all of F, induces a 4-regular nine-site set and every outside vertex has precisely one neighbor inside. Every pair inside then has its required common neighbors within the nine-set, giving SRG(9,4,1,2), the 3×3 rook graph. F was chosen not contained in such a grid. This excludes the last old family. Reversing all signs proves disjointness in the other class; ±3 cannot coincide since their classes differ modulo 9.

## Standard-library reproduction of local indexing and final minima

Run `python3 -B verify.py` ([standalone exact checker](verify.py)).
