# Bridges at a triangle and two complementary shell populations

Let \(T\) be a graph triangle and \(\{J_1,J_2\}\) two distinct rook grids containing it. At \(x\in T\), the unique line of \(J_i\) through \(x\) other than \(T\) is denoted \(L_i^x\). A bridge at \(x\) is a genuine grid \(G_x\) containing the two lines \(L_1^x,L_2^x\). It is unique if present: grids containing the same line have off-line prisms which are entire components of its cubic triangle wing, so two distinct grids sharing that line share no off-line point. Denote the number of available bridges by \(k(T;\{J_1,J_2\})\).

Bridges at different vertices are disjoint. They intersect \(J_1,J_2\) exactly in their named lines by the same shared-line observation; for different roots these are parallel disjoint lines within each \(J_i\). If an outside site belonged to both bridges, as a grid vertex off each named line it would have a neighbor in each of two different lines of \(J_1\). This contradicts one-domination by \(J_1\). Any such pair of bridges therefore presents a perpendicular double: the two line pairs \(L_i^x,L_i^y\) are matched in, and completed by, \(J_i\). Conversely a perpendicular double recovers the base triangle: its two grid centers (at the crossings) are matched, and their unique common neighbor is the common rung cap. The two completing grids, and hence the base pair, are also unique. Thus
\[
 D_\perp=\sum_{T,\{J_1,J_2\}}\binom{k(T;\{J_1,J_2\})}{2}.
\]

At a fixed vertex \(x\) the seven rooted triangles are axes of its clean grid graph \(\Gamma_x\), one edge for a grid on two axes. A clean triangle in \(\Gamma_x\) yields exactly three bridge flags at \(x\), according to which of its axes is chosen as the base. The converse is immediate from the two base grids and bridge. Hence, if \(g_T\) counts grids through \(T\), the preceding formula, \(\binom{k}{2}\ge k-1\), and the [canonical perpendicular double injection](perp-grid-pair-unique.md) imply the actual complementary norm bound
\[
 N_{18}^{+,{\rm nonunit}}\ge 2D_\perp\ge
     2\max\!\left(0,\ 3\sum_x \#K_3(\Gamma_x)-\sum_T\binom{g_T}{2}\right).
\]
This is oriented \(N_{18}^{+,{\rm nonunit}}\).

If all three bridges are present, let \(F\) be their twelve opposite-square sites. Then
\[
 1_F-1_T=\sum_{x\in T}1_{G_x}-1_{J_1}-1_{J_2}
\]
is an actual charge-one norm-15 \(+3\) field, i.e. \((A-3I)(1_F-1_T)=\mathbf1\) and the ordinary squared norm is fifteen. The right side accounts for the three centers with coefficient \(-1\), cancels all twelve arm sites, and leaves the twelve square sites with \(+1\).

This second map is also injective. For two representations of the same \(F,T\), consider their squares at **different** roots \(x,y\). They cannot share an edge: its unique cap within each respective bridge is a side-line arm adjacent to the corresponding root, lying in two distinct physical wings of \(T\). They cannot share an opposite pair either: its two common neighbors are the other square corners, forcing the whole square and therefore a shared edge. So different-root squares intersect in at most one point. Each square of the first representation has four vertices, and thus shares at least two with the corresponding same-root square of the second. A shared adjacent pair gives a common edge-cap line and both grids contain the same root outside that line, forcing equality; a shared nonadjacent pair determines the whole square and also the grid. Therefore all three bridges agree. Any pair of them has exactly two good cross lines by the [disjoint-grid theorem](disjoint-grids-two-cross-prisms.md), and their completions recover \(J_1,J_2\). In particular the count of base pairs with \(k=3\) is at most the actual \(F^+(1,15)\) population. This does not rule out the three-bridge family.
