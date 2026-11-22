# Triangle neighborhoods when every square has a prism

The [full-coverage theorem](saturated-choice.md) now forces a saturated triangle, allowing any number of grids.

Assume every induced square of a Conway graph belongs to a prism. Some triangle then has one of 35 specified 39-site neighborhoods up to labeling. When there are no rook grids, four neighborhoods suffice. The [saturated-line theorem](covered-spread.md) also forces a partition into 33 triangles in the grid-free case. Allowing grids gives [three global alternatives](covered-grid-choice.md).

## Fixed and moving labels

At a triangle take the three wings $P,Q,R$, label $Q$ and $R$ directly from $P$, use the same letters for their three mate involutions, and let $U$ be the matching from $Q$ to $R$. Exactly $t=|\mathrm{Fix}(U)|$ disjoint prism partners of the root triangle occur. At its three edges, the one-or-two-direction condition from the [square degree proof](square-profiles.md) implies that whenever $U(i)\ne i$,
$$P(i)=Q(i)=R(i),\qquad U(Q(i))=R(U(i)).$$
For the last equation take the matched pair $Q_i,R_{U(i)}$ at the third edge. Since $U(i)$ also moves, these equalities give $UP(i)=PU(i)$. The moving set is closed under the common mate involution: if $P(i)$ were fixed the last identity would force $i$ fixed. Its complement is likewise closed. In particular $t$ is even.

On the fixed part, any two coincident mates force all three to coincide at that label. Indeed a square at the two corresponding roots has two directions, so its covered four-cell is a grid; the third-wing sites at the two given labels must be mates too. A common mate pair gives one grid through the root triangle. The remaining fixed mate edges are three pairwise disjoint perfect matchings. On the moving part, $U$ permutes mate axes. On each axis cycle its only twist up to swapping signs on the axes is the parity of the sign changes. A positive one-cycle is fixed and a negative one-cycle would give a six-site component $K_{3,3}$, violating the common-neighbor bound. Thus every moving axis cycle has length at least two.

Summing $t$ on the 231 triangles counts each prism twice. Since there are at most 851 prisms there is a triangle with $t\le6$ by evenness. Enumerating the fixed matchings up to relabeling preserving the first one and the signed cycle partitions on the rest gives 13, 6, 10 and 8 templates at $t=0,2,4,6$, respectively. The [checker](covered_square.py) generates all 37 before the next exclusion.

## Excluding a single six-cycle

Suppose $t=0$ and $U$ is a six-cycle on the mate axes, with either twist. Number the axes cyclically so that $U$ takes axis $i$ to $i+1$. A far site gives two distinct axes in each wing, say $I,J,K$ in wing order. If axes match across a direct transfer, the corresponding selected signs must match too. Opposite signs across aligned mates already have the two common neighbors given by the two mates. Thus a matched axis contributes an actual cross-wing edge among the six contacts.

In each wing the two sites of a far point belong to different axes. The square formed by that far point, the wing parent and those two contacts must be covered. At least one contact's triangle partner with the far point belongs to its four-cell (a flip). All four points of this particular cell are exterior to the root triangle since both axes lie in the wing. Consequently at most one contact in each wing can be matched to another of the six wing contacts. Two internal edges among the six would be disjoint and would together use at least two contacts from one wing. Therefore
$$|I\cap J|+|I\cap K|+|(J+1)\cap K|\le1.$$
Exactly 1,053 unsigned words obey this condition. An integer linear certificate assigns weights to pairs of the 36 visible sites, using only their wing and axis labels. Every unsigned word contributes a total weight at most zero. On the other hand the number of exterior sites containing each pair $u,v$ must equal $2-A_{uv}-|N_{39}(u)\cap N_{39}(v)|$. These required multiplicities have weighted sum 900 for both twists. The checker stores the short lists of cyclic pair weights and directly verifies both contradictions. Thus 35 templates suffice.

## The grid-free covered case

At each point the seven incident triangles give seven axes. Each pair of axes has a dirty four-cell with exactly two parallel flips. Direct the pair toward the axis whose line is a prism partner direction, using the same convention for all pairs. More explicitly an axis for line $L$ receives a contribution from $M$ exactly when the two signs of $M$ at their common root extend to transversal prism partners of $L$. Each axis pair contributes to exactly one of its two lines. At a point the seven numbers $t_L/2$ thus sum to 21.

A dirty incoming or outgoing degree of one cannot occur by the [covered-root circulation equation](../../conway-99-involution/uncovered-squares/covered-root/Theorem.md): on each arc a circulation has a nonzero evaluation at a point of its own cell. A solitary incident arc at either role therefore contradicts conservation. In the absence of grids this excludes the values one and five for $t_L/2$. The odd sum forces at least one of the seven values to equal three. Choose such a line, so $t=6$. Its three fixed matchings are pairwise disjoint because no grid is present. Only two labeled fixed types remain up to simultaneous relabeling, and the three moving axes form one cycle of either twist. These give four templates in total.

## A point-line matrix identity

Continue to assume full square coverage, allowing grids. Let $N$ be the point-versus-triangle incidence, $P_*$ the adjacency on 231 lines joining prism partners, $D_t$ the diagonal of their degrees $t_L$, and $R$ the point-versus-rook-grid incidence. Then
$$N(P_*+D_t/2)N^t=20I+5A+J+RR^t.$$

At a point $p$ the seven values $t_L/2$ sum to 21 plus the number of grids through $p$. Each of the 21 axis pairs at $p$ contributes once for a covered nongrid cell and twice for a grid. Distinct intersecting lines cannot be prism partners. This proves the diagonal equality. For adjacent $p,q$, let $L$ be their line and $g_L$ the number of its grids. The number of prisms using $pq$ as a matching edge is $(12-t_L)/2+g_L$. On the moving labels the wing mates align in pairs. On the fixed labels an aligned mate pair gives exactly a grid. Adding the diagonal contribution $t_L/2$ gives $6+g_L$. For nonadjacent $p,y$, the terms count one prism for each direction of their square. The count is one plus the number of grids containing their square, because a covered two-direction four-cell is a grid. Distinct grids cannot share a square.

In particular, if all squares are covered and the graph is grid-free, $N$ has full row rank 99 over the binary field. If $N^t x=0$ then $(A+I)x=0$ because $NN^t=7I+A$, and $Jx=0$ because each point lies on seven lines. The displayed identity modulo two also gives $(A+J)x=0$, forcing $x=0$.
