# A point on all 21 possible grids forces an uncovered square

The subsequent [signed matrix argument](complete-point-exclusion.md) excludes such a point altogether, and [at most fifteen grids](seventeen-exclusion.md) occur at any point. The earlier conditional argument is recorded below.

If a Conway graph has a point on all 21 possible nine-point rook grids, it has **at least 136 distinct induced squares outside every triangular prism**. If every induced square is covered, each point belongs to at most **17** grids. This argument is independent of the five-grid boundary enumeration.

Fix a point $o$ and label its seven incident triangles by $1,\ldots,7$. Each supplies two neighbors of $o$, given opposite signs. For a two-element set $A$ of labels, $C_A$ consists of the four points having one signed parent on each of those two axes. A pair of parents on different axes has exactly one common neighbor other than $o$. These 84 cell points, the fourteen signed parents and $o$ account for the whole graph.

Call a cell clean when the four points, the four parents and $o$ form a rook grid. Its four cell points form a square, with edges changing one sign. A cell point has no neighbors in another cell sharing one of its axes: for each parent on that axis the common-neighbor quota with the cell point is already attained in the nine-point grid. If $A,B$ are disjoint and both clean, the edges between $C_A$ and $C_B$ form a perfect matching. Indeed each point of $C_A$ has exactly one contact with the rook grid of $B$ and sees none of its parents or center. Write $f_{AB}$ for this bijection.

## Triangles between cells

Assume full square coverage. Fix a clean cell $A$ for which all ten cells disjoint from $A$ are clean. The following argument first proves that the four points of $C_A$ use the same matching of the Petersen graph.

Each $y\in C_A$ sees one point in each of those ten cells. Its other four neighbors are two signed parents and two internal flips, paired with one another by their triangles. Consequently the ten external neighbors form five pairs, each pair in cells indexed by disjoint two-subsets of the remaining five axes. Thus each $y$ chooses a perfect matching $M_y$ of the Petersen graph $KG(5,2)$, whose edges join disjoint two-subsets.

For $B$ disjoint from $A$, call an edge $yy'$ of the square $C_A$ aligned if $f_{AB}(y),f_{AB}(y')$ are adjacent in $C_B$. A bijection between two squares either preserves all four edges or aligns just two opposite edges. In particular, the complementary pair of an aligned edge is also aligned. For an aligned edge the four vertices form an induced square. The caps on its two internal cell edges are signed parents on different axes and cannot be adjacent.

**A single covered aligned square forces all four cross edges at $AB$ to have their caps in the same third cell.** Indeed the caps on the two cross edges of that square must be adjacent. Each cap is in a cell indexed by two of the three axes outside $A\cup B$. Distinct such cells share an axis and are clean, so have no connecting edges. Both caps are therefore in the same cell $D$. The path matching $f_{DB}f_{AD}$ agrees with $f_{AB}$ on the two aligned points. Both are bijections on four letters. On the complementary two points $v,w$ they must agree or swap values. A swap would give a third common neighbor of $v$ and $f_{AB}(w)$ via $D$: the points $w$ and $f_{AB}(v)$ already supply two because the complementary pair is aligned. These endpoints are nonadjacent by the matching property. The swap is impossible. Hence all four triangles complete in $D$.

Under full coverage this holds for each of the ten cells disjoint from $A$, so each of the four points of $C_A$ chooses the same Petersen matching. This conclusion remains valid at a clean $A$ when all ten cells disjoint from $A$ are clean, irrespective of which other cells are dirty.

## The contradiction across axes

If $o$ lies on all 21 grids, the preceding result applies to every cell. It assigns a unique third cell to each edge between two disjoint base cells, agreeing at both ends. This decomposes the edges of $KG(7,2)$ into triangles. For each omitted axis $i$, the triangles that omit it give a partition of the fifteen pairs on the other six axes into five perfect matchings of $K_6$. Indeed in the Petersen matching at any cell $A$ avoiding $i$, exactly one of its five pairs of disjoint cells avoids $i$: among the ten Petersen vertices, four contain $i$ and they belong to four different matched pairs. This gives exactly one of the five triangles through $A$ omitting $i$.

Now omit $i$ and $j$ in turn. Restrict both resulting factorizations to the common five axes. Each becomes a perfect matching of the Petersen graph on the ten surviving two-subsets: from each factor of $K_6$, delete the edge using the sixth axis, leaving two disjoint pairs. The two Petersen matchings share an edge, say between $A,B$. The factorization omitting $i$ completes $A,B$ by a cell containing $j$; the one omitting $j$ completes them by a cell containing $i$. These are two different third cells for the same edge $AB$. This is the contradiction. The checker also directly lists all six factorizations for each omitted axis and confirms that no two choices for the first two axes have disjoint sets of base edges.

Finally, if there is any dirty cell at a covered point, the [root flow equations](../../../conway-99-involution/uncovered-squares/covered-root/Theorem.md) forbid incoming or outgoing degree one. In the bipartite graph on source and target copies of the axes, every vertex incident with an arc then has degree at least two. A nonempty simple bipartite graph with this property has at least four edges. At least four of the 21 cells are therefore dirty, proving the stated bound of 17.

## Counting uncovered squares without assuming coverage

Suppose all 21 cells at $o$ are clean, now permitting uncovered squares. The seven signed axes and the matchings between disjoint cells still exist. Call a cell variable if its four points do not all choose the same Petersen matching. The argument with two omitted axes shows some cell is variable, since that argument used only constancy of the matchings.

Every variable cell has at least eight disjoint cells for which the third cell depends on the chosen point. Indeed two of its different Petersen matchings agree on just one edge and therefore disagree on the partners of eight vertices. At each corresponding disjoint cell, the reciprocal bijection uses different third cells at different points too. Such a cell is variable. Let $m$ denote the number of variable cells. For the base adjacency $K$ on the 21 two-subsets, let $P$ be the seven-by-21 incidence matrix of elements and pairs. Then $K=J+I-P^tP$ and $K\mathbf1=10\mathbf1$. The indicator of the variable cells, centered by $m/21$, gives
$$8m\le 10m^2/21 + m-m^2/21.$$
Thus $m\ge17$.

Counting the pairs of disjoint cells with varying third cell from both ends gives at least $8m/2\ge68$ different pairs. Each such pair has at least two aligned edges and the single-square implication above shows that every one of these aligned squares is uncovered. Each square uses points from exactly its own two cells. This proves the bound of **136**.
