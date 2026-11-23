# A perpendicular double uniquely determines its complementary norm-18 field source

Use the [at most two good cross-lines theorem](disjoint-grids-two-cross-prisms.md). A disjoint pair of grids \(G_0,G_1\) with two perpendicular good cross lines has a canonical complementary integral \(+3\) field
\[
 c=1_{G_0}+1_{G_1}-1_{J_0}-1_{J_1}.
\]
Its unique double is negative, at the common rung cap. Its eight-site positive support \(F\) is the disjoint union of the two diagonal induced squares of \(G_0,G_1\), joined by a perfect matching. In fact the field determines the unordered grid pair; there is no multiplicity of three.

Suppose two pairs give the same \(c\). If they give the same partition of \(F\) into its two diagonal squares, they agree: a square determines a true grid by its four side-edge caps and the uniqueness of completion from eight common sites.

For different partitions, let \(M,M'\) be the perfect matchings of the cubic graph on \(F\) left after deleting the two square cycles of each partition. They cannot share an edge \(vv'\): at \(v\) both partitions would then choose the same other two incident edges, a fixed two-edge path. Its endpoints already share \(v\) and have at most one further common neighbor, so the square through \(v\), and hence its complementary square, would be the same. Therefore \(M,M'\) are disjoint, and the remaining edges form a third perfect matching \(M''\). Each square of each partition is a union of exactly two \(M''\)-edges, since its cycle alternates \(M''\) with one other matching. The two distinct partitions of the four \(M''\)-edge blocks into pairs intersect each other in exactly one block per square pair. In particular the four intersections between a square from the first pair and a square from the second each consist of an actual side edge.

Write \(H_0,H_1\) for the second grid pair. The two pairs consist of four distinct grids: if \(G_i=H_j\), then its second square would be disjoint from the other \(G\)-square, contradicting the two-site intersection just proved. Complete each of the four shared square edges to its unique graph triangle \(X_{ij}\), lying in both \(G_i,H_j\). In a given grid these shared edges are opposite sides of its diagonal square (they are the two disjoint \(M''\)-edges), hence their two completing triangles are disjoint parallel lines in that grid. Thus \(X_{00},X_{01},X_{11},X_{10}\) are the four distinct corners of a good-prism rectangle, with the edge-completing grids the original four grids. Opposite pairs are anticomplete also directly by one-domination: for example \(X_{00}\) uses its \(G_1\) contact matching \(X_{10}\) in \(H_0\), and so cannot see \(X_{11}\subset G_1\).

By the [bad-diagonal theorem for a good rectangle](bad-prisms.md#rectangles-of-good-prism-mates), the two leftover parallel lines \(L_0,L_1\) of \(G_0,G_1\) form a bad prism. But each \(L_i\) contains the center of \(G_i\) opposite its diagonal square, since the two shared lines are the parallel lines through the two respective sides of that square. This center is exactly the intersection of the two original perpendicular good lines. Both lines through the center in \(G_i\) are therefore good across to the other grid. Since \(L_0,L_1\) form a prism across the unique perfect matching of the disjoint grids, their prism must be good, a contradiction.

Thus disjoint grid pairs with a perpendicular double inject into the antipodal nonunit \(+3\) norm-18 fields, and
\[
 D_{\perp}\ \le\ N_{18}^{+,{\rm nonunit}}/2
\]
for **oriented** \(N_{18}^{+,{\rm nonunit}}\). This strengthens the earlier count by a factor of three and is unconditional in rank. It does not assert that either population is nonzero.
