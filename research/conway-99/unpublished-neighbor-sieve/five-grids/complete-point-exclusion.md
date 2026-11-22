# No point of a Conway graph lies on all 21 grids

**Theorem.** In any strongly regular graph with parameters $(99,14,1,2)$, every vertex lies on at most **17** induced three-by-three rook grids. No symmetry, rank or prism-coverage hypothesis is needed.

Suppose a point $o$ lies on all 21 grids. Use the seven signed axes and the 21 four-point cells $C_a$ from the [cell description](complete-point.md), where $a$ is a two-subset of seven axes. Each cell induces a four-cycle. Cells sharing one axis have no edges between them. Between disjoint cells there is a perfect matching, and no point of either cell sees a signed parent of the other. These assertions follow from the one-neighbor property of the grids and use no square coverage.

The [four-cell exclusion](seventeen-exclusion.md) further lowers the bound to fifteen.

## Even triangle counts on three disjoint cells

Fix two disjoint cells $a,b$, identify their four points by their matching, and denote the opposite-point involutions of their two four-cycles in these coordinates by $d_a,d_b$. Exactly three cells $c$ are disjoint from both. The two-step matching from $a$ through $c$ to $b$ induces a permutation $h_c$ of the four points. Using permutation matrices, with rows giving starting points, the cross block of the graph equation gives
$$\sum_c h_c = I+d_a+d_b.$$
In fact the matching between $a,b$ is $I$, the four-cycle adjacencies are $J-I-d_a,J-I-d_b$, and the full demand for two-step paths is $2J-I$. No signed parent can supply a common neighbor.

The number of graph triangles with one vertex in each of $a,b,c$ equals the number of fixed points of $h_c$. For each of the four starting points exactly one of the three permutations fixes it, by the diagonal equation. No permutation on four letters has exactly three fixed points. The only possible list with an odd entry is therefore $(2,1,1)$. In that list one permutation is a transposition and the other two are three-cycles fixing different letters. Their sum cannot be symmetric: at the letter fixed by the first three-cycle but moved by the other, the moving three-cycle has different predecessor and successor. The transposition matrix and the right side are both symmetric. This proves that every triangle count is even.

At each of the four points in $C_a$, the ten neighbors in disjoint cells pair up by triangles. Their cell partners form a perfect matching of the Petersen graph on the ten two-subsets of the other five axes. There are six perfect matchings, each edge lies in two of them, and every two different matchings share one edge. Let $x_i$ count how many of the four points choose matching $i$. Each $x_i+x_j$ for $i\ne j$ is one of the even triangle counts just proved. All six $x_i$ have the same parity and sum to four. Thus the four points use one matching four times or two different matchings twice each.

## A finite classification on seven axes

Give a triple of disjoint cells weight equal to half of its triangle count. Fix an omitted axis. For a cell $a$ avoiding it, exactly one pair in each of its four Petersen matchings avoids that axis: four of the ten Petersen vertices use the omitted axis, all in different matched pairs. Consequently the weights of the triples containing $a$ and avoiding the omitted axis sum to two. Equivalently, on the remaining six axes, take a multiset of perfect matchings of $K_6$ in which every edge occurs exactly twice. For each disjoint cell pair $a,b$, the weights of its triples across all omissions must also sum to two, since the four crossing edges each lie in one triangle.

The [standard-library checker](complete_point_exclusion.py) enumerates these multisets by selecting all factors covering the first unfilled edge with its outstanding multiplicity. There are 27 choices per omitted axis. Assign the omissions in order, discarding only when a disjoint cell pair has already used more than its weight budget of two. The counts of compatible prefixes of lengths zero through seven are
$$1,27,198,408,408,408,408,408.$$
For each complete assignment and cell $a$, compare its fifteen weights with the sum of indicators of two Petersen matchings, permitting repetition. Exactly 30 assignments pass at all cells. In every one, all 21 cells use two *different* matchings twice each. This numbering concerns the axes at one point and assumes no automorphism of the Conway graph.

In each cell order its two matchings by any fixed convention. For disjoint $a,b$, each matching at $a$ gives a third cell for the edge to $b$. If both give the same third cell, call the pair constant. The constant pairs form seven vertex-disjoint triangles on the 21 cells: each cell's two matchings share just one edge $bc$, and all four crossing edges between each pair in the resulting triple are completed in the third cell. For a nonconstant pair, transport between $C_a,C_b$ either preserves the ordering of the two groups or reverses it. Put $Z_{ab}=1$ or $-1$ respectively. Put zero everywhere else. The third-cell names determine this sign without choosing the four-point transport. In **each** of the 30 labeled cases, direct integer multiplication gives
$$Z^2=2Z+8I_{21}.$$
Reversing any cell ordering conjugates both sides by a diagonal sign matrix.

## The trace contradiction

Let $A$ be the full graph adjacency and let $V$ have 21 orthonormal columns $v_a$, each supported on its own four-point cell. Give $v_a$ values $+1/2$ on the two points of the first group and $-1/2$ on the other two. Set $W=AV-VZ$ and $L=V^tW$.

On a nonconstant neighboring cell the transport takes $v_a$ exactly to $Z_{ba}v_b$, so $W_a$ vanishes there. Its remaining support is confined to its own constant triple of cells and the signed parents on the two axes of $a$. In particular $L$ is supported within the seven diagonal triple blocks, where $Z$ is identically zero. Also $\langle W_a,W_b\rangle=0$ when $Z_{ab}\ne0$: the triples differ and the two axis pairs are disjoint. Therefore
$$\operatorname{tr}(ZL)=\operatorname{tr}(ZW^tW)=0.$$
The diagonal entry $L_{aa}$ comes from the four-cycle of $C_a$. A balanced two-plus, two-minus column on a square has adjacency eigenvalue $-2$ when its equal-sign pairs are opposite, and zero when they are adjacent. If $d$ cells use opposite pairs then $\operatorname{tr}L=-2d$.

Since the columns are centered, $A^2+A=12I+2J$ gives $V^t(A^2+A)V=12I$. Multiply by $Z$ and take the trace. Substituting $AV=VZ+W$ and using the two vanishing traces gives
$$0=\operatorname{tr}(Z^3+Z^2)+2\operatorname{tr}(Z^2L)
=504-32d.$$
Here $\operatorname{tr}(Z^2)=168$ and $\operatorname{tr}(Z^3)=336$. Thus $d=63/4$ would count cells, which is impossible.

## At least four cells fail at every point

For completeness this last step applies at an arbitrary point, including one with uncovered squares. For an axis pair $e$ let $S_e$ be its nine sites (center, four signed parents, four cell sites). Let $G=3I-A+J/9$ and $v_e=G1_{S_e}$. Since $G^2=7G$, its squared norm is $14(4-m_e)$, where $m_e$ is the internal edge count of the four-site cell: $S_e$ spans $14+m_e$ edges. Each cell site has internal degree at most two. If it has degree two then both its internal neighbors must be the two single-sign flips, by the common-neighbor counts with its signed parents and their opposite signs. Hence $m_e=4$ exactly for a grid.

For every axis $i$, the sum of $v_e$ over its six incident pairs is zero. Indeed the sum of the nine-site indicators is $(A+4I)$ applied to the indicator of the triangle on that axis, by counting positions in the cells. Multiplication by $G$ kills $A+4I$. Therefore in the simple graph of nongrid pairs on seven axes every nonisolated vertex has degree at least two. If there were only three nongrid pairs they would form a triangle, and the three axis equations would force all three vectors to vanish by alternation. One or two pairs are impossible by the degree condition. The trace contradiction excludes zero nongrid pairs, leaving at most seventeen grids.
