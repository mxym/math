# At most two good cross-line prisms between disjoint rook grids

Let \(G,H\) be two disjoint literal nine-site rook grids in a hypothetical \(\operatorname{SRG}(99,14,1,2)\). Every vertex outside a grid sees exactly one grid site: every pair in the grid already has its entire common-neighbor quota there, so no outsider can meet two, and there are ninety outside incidences across ninety outside sites. Thus the edges between \(G,H\) form a perfect matching \(\pi\).

A *good cross line* is a row or column \(L\) of \(G\) such that \(\pi(L)\) is a triangle and the matched prism \(L\cup\pi(L)\) completes to a rook grid. **At most two of the six lines of \(G\) are good cross lines.** No Seidel-rank assumption or graph-isomorphic matching of \(G,H\) is required.

Write \(q_v\) for the unique common neighbor of \(v\in G\) and its match \(\pi(v)\in H\). It is outside both grids, and all nine \(q_v\) are distinct because an outside site cannot see two vertices of \(G\). For a good line \(L\), its completing grid \(J_L\) is exactly
\[
 L\cup\pi(L)\cup Q_L,\qquad Q_L=\{q_v:v\in L\}.
\]
In particular \(Q_L\) is a triangle. Each \(q_v\) with \(v\notin L\) has exactly one neighbor in \(Q_L\): its only contacts in \(G,H\) are its own endpoints, so it has no contact in the first two lines of \(J_L\).

## Three parallel good cross lines are impossible

If all three parallel lines \(L_i\) of \(G\) are good, their disjoint images in \(H\) are a parallel decomposition of \(H\). The three \(J_{L_i}\) are disjoint and partition \(G\cup H\cup Q\), where \(Q=\{q_v:v\in G\}\). Every genuine grid indicator satisfies \((A-3I)1_J=\mathbf1\). Subtracting the two grid indicators from the sum of the three completing indicators gives \((A-3I)1_Q=\mathbf1\). So \(Q\) is 4-regular on nine sites and one-dominating outside. Every pair within \(Q\) has its full common-neighbor quota inside, giving the unique \(\operatorname{SRG}(9,4,1,2)\), a rook grid.

The three corresponding lines in each of \(G,H,Q\) are now nine disjoint triangles. The three grids and the three completing grids give the two array directions. Nonaligned pairs are anticomplete by the fixed matching/cap labels and the parallel partitions. This is the [forbidden nine-triangle rook array](README.md).

## Two parallel good lines forbid any perpendicular good line

Suppose rows 1 and 2 are good, and write \(A_i,B_i,Q_i\) for the corresponding triples in \(G,H,Q\), respectively. The third matched row \(P=A_3\cup B_3\) is a prism, since the two disjoint images \(B_1,B_2\) are parallel lines in \(H\). It is bad by the previous section. Also \(N=Q_1\cup Q_2\) is a prism: both cap rows are triangles and the edges between them are a perfect matching by the cap one-contact rule. The prisms \(P,N\) are disjoint and anticomplete. Comparing the four true grid indicators gives
\[
 (A-3I)(1_P-1_N)=(A-3I)(1_G+1_H-1_{J_{L_1}}-1_{J_{L_2}})=0.
\]
They have the same shadow. The height-two sites of a prism are exactly its three rung caps: an outside vertex sees at most one site on each face, and any cross nonedge already has its two common neighbors inside the prism. Therefore \(P,N\) have exactly the same cap triple \(Q_3\); \(N\) is also bad.

Now assume for contradiction that column 1 is good across the two grids. Its cap triangle is \(q_{11},q_{21},q_{31}\) in the usual rook coordinates on \(G\). It uses a rung \(q_{11}q_{21}\) of \(N\) and its unique cap \(q_{31}\). The other two members \(q_{32},q_{33}\) of \(Q_3\) cap the other two rungs of \(N\). Thus neither sees \(q_{11}\) or \(q_{21}\), since each can see at most one site on each of the cap triangles \(Q_1,Q_2\). Nor do they have any contact on the \(G,H\) lines of the perpendicular completing grid, since their corresponding labels are outside column 1. Its one-domination forces both of them to see \(q_{31}\). Hence \(Q_3\) contains at least two edges.

There are exactly fifteen edges in \(P\cup Q_3\) other than its cap-triple edges (nine prism edges and six cap incidences). With two cap-triple edges it is a forbidden 17-edge nine-set by the [nine-site density gap](../../conway-99-involution/grid-density-gap/README.md); with three it completes \(P\), contrary to badness. Thus two parallel good lines and a perpendicular one cannot coexist. Any choice of three good lines contains a parallel pair and is forbidden by one of the two cases.

## Counting the two types of double

Write \(D_{\parallel}\) and \(D_{\perp}\) for the unordered disjoint grid pairs having two parallel or two perpendicular good cross lines, respectively.

For the parallel type, the four matched line triangles \(A_1,A_2,B_1,B_2\) form a good-prism rectangle in the cyclic order \(A_1,A_2,B_2,B_1\); opposite pairs are anticomplete by the grid matching. Conversely either pair of opposite edges of a [good rectangle](bad-prisms.md#rectangles-of-good-prism-mates) gives two disjoint completing grids: the four triangle corners and their four edge-completion lines are disjoint. The other two rectangle edges join two marked parallel-line pairs in those grids. The two opposite-edge choices give distinct grid pairs (otherwise a completing grid would contain two anticomplete corner lines). Since the two good cross lines recover the rectangle, this gives
\[
 D_{\parallel}=2R\le 2B,
\]
where \(R\) counts good rectangles and \(B\) counts bad prisms, using the [rectangle-class forest](rectangle-class-forest.md).

For the perpendicular type let \(J_{\rm row},J_{\rm col}\) be the two completing grids and let \(q\) be the common rung cap at their intersection. Then
\[
 c=1_G+1_H-1_{J_{\rm row}}-1_{J_{\rm col}}
\]
is an actual integral neutral \(+3\) eigenfield. Its positive sites are the eight diagonal sites of the two grids, a disjoint union of two induced squares joined by the grid matching. Its unique double is \(-2\) at \(q\); the two rung endpoints and the four other cap sites are \(-1\). So \(c\) has squared norm 18. This sign is canonical for the antipodal line.

A fixed such \(c\) comes from at most three unordered disjoint grid pairs. Indeed one of its eight positive sites has exactly three neighbors in the positive support (two square neighbors and one matching neighbor). Choosing which is the matching neighbor leaves a specific consecutive two-edge path in the square. Its two endpoints have the chosen site and at most one additional common neighbor, forcing the fourth corner. The other square is the support complement. An induced square determines at most one true rook grid containing it: the four side edge caps are four distinct further required grid sites, giving at least eight common sites in any two proposed grids. If distinct their indicator difference would be a nonzero vector \(1_x-1_y\) in the \(+3\) eigenspace, which is impossible by its eigen-equation at \(x\). Thus there are at most three grid pairs for the fixed field, and
\[
 D_{\perp}\le \tfrac32 N_{18}^{+,{\rm nonunit}},
\]
where the latter number is **oriented**. These are structural exclusions and counts; no local pattern or graph existence is asserted.
