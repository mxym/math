# Disjoint rook grids have at most three good cross prisms

Let G,H be two disjoint literal nine-site rook grids in a hypothetical SRG(99,14,1,2). Every vertex outside a grid sees exactly one grid site: two are impossible because every pair in the grid already has its full common-neighbor quota there, and the nine grid sites contribute nine times ten outside incidences across ninety sites. Thus the edges between G and H form a perfect matching \(\pi\).

A *good cross line* is a row or column \(L\) of G for which \(\pi(L)\) is a triangle and the matched prism \(L\cup\pi(L)\) completes to a rook grid. At most three of the six lines of G are good cross lines; if there are three, their directional pattern is two parallel and one perpendicular. In particular the statement requires neither a rank assumption nor an isomorphic matching of the two grids.

Write \(q_v\) for the unique common neighbor of \(v\in G\) and its match \(\pi(v)\in H\). It is outside both grids, since each endpoint has exactly one neighbor in the other grid. The nine \(q_v\) are distinct: an outside site cannot see two vertices of G. Whenever \(L\) is good, its completing grid \(J_L\) is exactly \(L\cup\pi(L)\cup\{q_v:v\in L\}\); the three required sites are forced by their rung caps. Thus the corresponding cap line \(Q_L\) is a triangle. Moreover every \(q_v\) with \(v\notin L\) has exactly one neighbor in \(Q_L\): it has no neighbors in either of the first two lines (its only neighbors in G,H are its own endpoints), so its one contact with \(J_L\) must lie on \(Q_L\).

## Three parallel good cross lines are impossible

If all three parallel lines \(L_i\) of G are good, their disjoint images in H are a parallel decomposition of H. The three \(J_{L_i}\) are pairwise disjoint and partition \(G\cup H\cup Q\), where \(Q=\{q_v:v\in G\}\). Every genuine grid indicator satisfies \((A-3I)1_J=\mathbf 1\) on the graph. Subtracting the indicators of G,H from the sum of those of the three \(J_{L_i}\) therefore gives \((A-3I)1_Q=\mathbf 1\). Thus \(Q\) is 4-regular on nine sites and one-dominating outside; every pair within Q has its full common-neighbor quota inside, so it is the unique \(\operatorname{SRG}(9,4,1,2)\), a rook grid.

Now take the nine actual triangles indexed by the three lines of G, their corresponding lines in H, and their cap lines in Q. The three parallel partitions of G,H,Q give one direction of an array; the three \(J_{L_i}\) give the other. Nonaligned pairs are anticomplete because all three matchings between the three disjoint grids are the fixed rung labelings. This is exactly the [forbidden nine-triangle rook array](README.md), a contradiction.

## Two good rows and two good columns are impossible

Give G the usual coordinates and suppose rows 1,2 and columns 1,2 are good. Write \(q_{ij}\) for the cap in position \(ij\). The two tails \(q_{13},q_{23}\) must be adjacent. In fact \(q_{13}\) meets each of the cap columns 1,2 at its own row-1 entry, so cannot meet either \(q_{21}\) or \(q_{22}\); its required unique contact with cap row 2 must be \(q_{23}\). Symmetrically \(q_{31}\) is adjacent to \(q_{32}\).

Suppose \(q_{33}\) sees \(q_{ij}\) for \(i,j\in\{1,2\}\). Put \(i'=3-i\), \(j'=3-j\). The pair \(q_{ij},q_{i'3}\) already shares the two distinct neighbors \(q_{i3},q_{i'j}\) by the forced tail edge and the good rows/columns. Thus \(q_{33}\) cannot see \(q_{i'3}\). Its one contact with the other good row must be an intersection, and must be in column \(j'\) because column \(j\) already contains its contact \(q_{ij}\). But the diagonal pair \(q_{ij},q_{i'j'}\) already shares the other two intersections, so cannot share \(q_{33}\). Therefore \(q_{33}\) has no neighbor in the four intersections.

Its required contacts with the four good lines now give exactly the four tails \(q_{13},q_{23},q_{31},q_{32}\). In particular cap row 3 is a triangle. The images in H of the two good disjoint rows 1,2 are two parallel lines there, so the remaining row's image is also a line. Its matched prism therefore closes with this cap triangle. There are now three parallel good lines, already ruled out.

Any four good lines would contain three parallel ones or two lines in both directions. The asserted bound and only remaining three-line directional pattern follow.

## The bad pair forced by two good parallel lines

If exactly two parallel lines of G are good, their third matched line is a prism \(P\) which must be bad. The first two cap lines form a prism \(N\): each vertex of either cap line has exactly one neighbor in the other, by the one-contact rule proved above. These are anticomplete disjoint prisms. Comparing the four true grid indicators gives
\[
 (A-3I)(1_P-1_N)=(A-3I)(1_G+1_H-1_{J_1}-1_{J_2})=0.
\]
Thus they have the same shadow. In any prism the three sites with two prism contacts are precisely its rung caps: a cross nonedge already has two common neighbors inside the prism. Consequently \(P,N\) have the same three rung caps, exactly the remaining cap line. In particular \(N\) is also bad. This is a necessary family constraint and does not assume that a pair of disjoint grids, or the surviving two-plus-one pattern, exists.
