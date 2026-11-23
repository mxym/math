# A rank-40 norm-16 bound and a seven-cube complementary shell

> **Update:** [The seven-cube obstruction](norm16-no-six-cubes.md) proves that six matched cubes would force seven, and that seven are impossible. The norm-16 bound 6,062 under N20=0 therefore holds at all ranks. The conditional seven-cube profiles below document the earlier intermediate argument.

Use the [good rooted-triple packing](norm16-good-triple-cube.md). For any root and independent triple let m count its actual oriented norm-16 fields and g the good ones. Four or more good fields share one signed eight-site cube Q; their other signed sites are disjoint induced cubes.

## Rank 40 with no norm-20 fields

Five good fields at one seed would have ordinary graph-coordinate Gram matrix 8(I+J) of size five: each has norm 16, and each pair agrees on Q and is disjoint off Q. Its determinant is 8^5·6, a unit modulo seven. In the [original mark lattice](../../maximal-marked-lattice/README.md), each integral neutral eigenfield divided by the square root of seven belongs to the dual and pairs with the vertex marks by its own site values. Seven times the dual pairing therefore gives the graph-coordinate dot product on the elementary discriminant at seven, of dimension 44−r. At rank 40 this dimension is four, so a Gram of rank five is impossible. Hence g≤4. This step does not require N20=0.

When N20=0 the packing already gives m≤8 and, when g≥4, m≤6. Thus m+2g≤14 at every seed of a rank-40 graph. Summing over the 27,720 seeds counts each of the N16 oriented fields 32 times in m and at least 16 times in g. Consequently 64N16≤388080, giving **N16≤6062** by antipodal parity. This excludes neither rank 40 nor graphs with norm-20 fields.

## The seven-cube family at any rank

If g=6, write the good fields f_i as q+c_i, where q is the signed indicator of Q and c_i the six complementary cubes. Between Q and each complementary cube there is one opposite-sign matching, since both cubes are three-regular inside a four-regular bipartite norm-16 support. Between any pair of complementary cubes there is one matching preserving the signs of c_i,c_j: f_i−f_j is itself norm 16 and uses opposite colors on the two complements. Reverse the coloring of Q, leaving the complementary colors unchanged; then all cross-cube matchings preserve colors.

Each cube has 20 outside double-contact witnesses: one per cube edge and two per antipodal pair of opposite parity. Each witness has at most one contact on each parity, because pairs on one parity already have both common neighbors inside the cube. None of the 20 witnesses lies in the other six cubes, since cross-cube edges are matchings; they use all 40 incidences from the cube to the 43 vertices outside the union. Thus an exterior vertex either misses a given cube or takes one of each sign. The total signed parity indicator is consequently an actual unit +3 eigenfield, of norm 56. On the union its adjacency sum is six same-color minus three opposite-color incidences times its sign; outside it is zero. Its opposite-color connected components recover all seven cubes. In particular if Q7 counts these unordered cube families, then 2Q7 is at most the oriented unit complementary norm-56 population.

Such a family accounts for 56 six-good seeds, choosing any of its 56 vertices and that vertex's three cube neighbors, orienting the source norm-16 fields to make the vertex positive. A six-good seed determines its family uniquely because the graph-side good bound is at most six. Under N20=0, the packing gives m+g≤11 except when g=6, where m+g=12. Therefore
```
48 N16 ≤ 304920 + 56 Q7.
```
Without a seven-cube family the bound is 6352 by parity. Reaching 6496 would require at least 123 families, or at least 246 corresponding oriented complementary fields. These are conditional upper bounds on actual counts, not an assertion of nonexistence of a seven-cube family.

## Exterior verification profiles

Let S denote the 56-site indicator and t_x the number of cubes contacted by an outsider x (zero on S). Each cube is hit by 20 outsiders; each pair by eight common outsiders. For the second count, the sixteen same-positive pairs across the two named cubes have common-neighbor budget 32−4=28, as four are matching edges. The other five cubes each supply four incidences. The two named cubes supply none: any neighbor in the same cube has opposite color while matching contacts across cubes preserve color. The remaining eight are precisely the common outsiders.

Thus sum t=140, sum t²=476, and sum (t−3)(t−4)=12 over the 43 outsiders. The strongly regular identity applied to A S=9S+2t gives At=56·1−39S−10t. Heights six and seven are impossible by nonnegativity. A height-five site has four exterior neighbors of total height six. Height zero already uses twelve units of the quadratic excess and cannot coexist with a five, which uses two. At most one height-one site can coexist with a five, giving neighbor-height sum at least 1+2+2+2=7, another contradiction. Thus all heights are at most four.

Enumerating the nonnegative histogram with 12n0+6n1+2n2=12 and the given count and first moment leaves four options. In the option with two height-one sites, there are 26 height-three and 15 height-four sites, no others. Each height-one site needs twelve exterior neighbors of total height 46, so it cannot meet the other height-one site and needs ten height-four neighbors. Those two ten-sets would share at least five, violating the common-neighbor bound. The remaining necessary histograms, in height order 0 through 4, are
```
(1,0,0,28,14), (0,1,3,23,16), (0,0,6,20,17).
```
If B_i indicates outsiders hitting cube C_i, then A1_Ci=2·1_Ci+S+2B_i; the same strongly regular identity gives (AB_i)_x=8−t_x−3B_i(x) at every exterior x. None of these three profiles is asserted realizable.
