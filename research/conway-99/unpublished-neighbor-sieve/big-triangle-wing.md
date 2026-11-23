# Every vertex lies on a triangle with a large wing component

Assume G is a strongly regular graph with parameters (99,14,1,2). For a triangle T, its wing graph W(T) is induced by the 36 vertices adjacent to a point of T but not in T. This is partitioned into three 12-site wings by the unique neighbor in T. A grid is an induced 3-by-3 rook graph.

**Theorem.** Every vertex of a hypothetical SRG(99,14,1,2) lies on a triangle whose wing graph has a connected component of order at least eighteen. Consequently at least 33 distinct triangles have such a component. This is not a connectedness theorem for all 36 wing vertices and does not assume or bound the number of grids.

## Ordinary local chart and real defects

The neighborhood of o consists of seven matched pairs, called axes. Every exterior vertex has exactly two neighbors in the neighborhood of o; these belong to distinct axes, since an edge has only one common neighbor. Conversely every specified pair of signed parents on two distinct axes has precisely one common neighbor other than o. The exterior 84 vertices are accordingly partitioned into four-point cells C_e for each axis pair e. Let S_e be the nine-point set given by o, the four signed parents on e, and C_e. Set
```
M = 3I−A+J/9,     v_e=(A−3I)1_(S_e)−1=−M1_(S_e).
```
The strongly regular identity gives M²=7M and Av_e=−4v_e. These v_e have coordinate sum zero and vanish at o and all first-layer points. For an exterior vertex x, write d_e(x) for its number of neighbors in C_e. The defect value is
```
d_e(x)−2   if x∈C_e,
d_e(x)     if the cell of x is different and intersects e in an axis,
d_e(x)−1   if that cell is disjoint in axes from e.
```
Indeed first-layer neighbors contribute 2,1 or 0 to the adjacency sum on S_e, and the coefficient at x in 1_(S_e) is 1 exactly in the first case. The squared norm is 14(4−m_e), where m_e is the number of edges internal to C_e: there are 14+m_e edges in S_e and M²=7M.

For a cell vertex on a given axis, exactly one exterior neighbor through that axis has its same signed parent (the triangle cap of that edge), and exactly one has the opposite signed parent (the second common neighbor with that parent, beside its own parent). Thus d_e(x)≤2 in the own cell; at degree two the two neighbors are precisely the two sign flips, since the diagonal would consume opposite-sign slots on both axes and leave an impossible same-sign neighbor on both. Consequently v_e=0 precisely when C_e is the sign square, which together with its four parents and o is the rook grid. Such cells are called clean; the other cells are dirty. Every grid through o is of this form: its four neighbors of o determine the two axes, and its remaining four sites then have the four signed-pair labels.

We will also use that a dirty cell cannot have m_e=3. If it did, v_e would be a nonzero integral neutral field of norm14. It is unit: if an entry has absolute value ≥2, orient to a positive one and subtract d_i=(3I−A)e_i at that index. Since ||d_i||²=23 and v·d_i=7v_i, the new cost is at most 14+23−28=9 while its coordinate sum is +11, impossible for an integer vector. There are therefore seven vertices of each sign in v_e. Each negative vertex has at least four positive neighbors by the eigen-equation. Hence the seven negative sites account for at least 7·choose(4,2)=42 common-neighbor incidences of positive pairs, all the available 2·choose(7,2); the positive side similarly consumes all the allowances of negative pairs. The three edges of C_e form a four-site path: otherwise its isolated fourth site has v_e=−2, which is impossible. Its degree-two vertices have both flips, so the cell path is the standard square with one flip missing. The two endpoints both have v_e=−1 and share the signed parent on the missing flip, outside the positive support, a contradiction.

## Split the axes by their actual wing components

For any triangle, each vertex outside it meets at most one triangle point. Within each wing the edges form a perfect matching, and between each pair of wings the edges also form a perfect matching. This is the standard triangle decomposition (see the [triangle-array notes](triangle-array.md)). In fact a vertex in the wing of a first triangle point has exactly two common neighbors with the second triangle point, one on the triangle and the other in the second wing. At a triangle T_a on axis a through o, the wing rooted at o consists of the twelve signed parents on the other six axes. Its internal matching puts both signed parents on any given other axis into the same component. The matches from those two parents into the other two wings give the four cell sites on that pair with a. It follows that each component of W(T_a) consists of 2k such parents and 4k corresponding cell sites, for a subset of k of the other axes. Thus the sizes of its components are 6k with these subsets partitioning the other six axes.

For each such component D and its associated incident axis pairs E_a, the exact identity
```
Σ_(e∈E_a) v_e=0
```
holds. To prove it without assumptions on the far sites, put h=k·1_(T_a)+1_D. The left side is b=(A−3I)h−k1=−Mh, since the coordinate sum of h is 9k. At a point of T_a, the neighborhood h-sum is 2k+2k=4k. At a point of D it is k+3, from the one triangle neighbor and the three neighbors in the cubic component. Therefore b vanishes on the support of h. The identity M²=7M gives ||b||²=−7 h·b=0, as required.

A component with k=1 thus consists precisely of the wing part of a clean grid. Conversely a clean C_e gives such a component: in W(T_a) its six sites from the grid have degree three there and hence no other wing neighbors. The assertion is symmetric in the two axes of e.

Make a split axis graph: split each of the seven original axes into one vertex for each of these component subsets, and attach the single edge e for an original axis pair to the corresponding split vertex at either end. Each split vertex has degree k and carries the unsigned zero-sum relation just proved. This graph is simple because each pair of original axes occurs only once. Distinct split components at the same axis give no edges between the corresponding cells in the original graph, since those cells lie in different components of the wing graph of that axis triangle.

## Dirty cycles and the three outside cells

Assume all wing components at o have size at most twelve, so k is 1 or 2. Clean edges each join two degree-one split vertices, and all unique possibilities at dirty split vertices are degree two. Thus the dirty split graph is a disjoint union of cycles. Along a cycle the nonzero v_e alternate v,−v, so its length is even. Two distinct cycle edges of the same sign cannot share an original axis: the own-cell values of v_e are nonpositive and somewhere strictly negative, whereas the other column is nonnegative there if the axes intersect. Hence each sign uses pairwise disjoint original axis pairs and there can be at most three edges of either sign. The cycle length is four or six. Its original axes are all distinct: a repeated axis at distance two would repeat an axis pair, and at distance three in a six-cycle it would make two of the same-sign axis pairs intersect.

For a cycle with axis set U, v vanishes on every cell using an axis in U except the cycle cells themselves. In fact such a cell has a different split component at the shared axis from the two incident cycle edges. There are no original edges to either corresponding cycle cell, and its defect value there is therefore zero. On a cycle cell, the own column is nonpositive while any other same-sign column is at least −1 there, since they are disjoint axes. This makes v unit on all cycle cells. On a cell wholly outside U, all cycle edges are disjoint in axes from it; comparison with both signs gives unit values there too.

A six-cycle has only one axis left outside U, so v is supported on at most 24 sites in its six cells. Its nonzero norm is a multiple of fourteen; the only possibility is 14, already excluded for a dirty cell. Thus all cycles have length four.

For a four-cycle, the support has at most 28 sites from the four cycle cells and the three cells on the three outside axes. The norm is 28 since 14 is excluded. Every site of these seven cells is therefore nonzero, taking a unit sign. Each cycle cell is uniform in sign, and its own internal graph is a perfect matching by d_e(x)−2=−1 there. At a site x of a cell on the three outside axes, each of the two opposite-sign cycle cells contributes two neighbors to x (use d_e(x)−1=+1 for the appropriate alternated columns); the two same-sign cycle cells contribute none. They supply all of the required −4v(x). Thus the signed sum over any further neighbors within the three outside cells is zero.

If an outside cell is dirty, it belongs to a four-cycle of its own and its internal graph is a matching. Its signed neighbor sum within the outside cells cannot vanish if it has no edges to the other two outside cells, since its own matching gives exactly one neighbor of nonzero sign. Edges between two distinct outside cells can occur only when they share the same split vertex at their shared axis. Hence any dirty outside cell must have a second dirty outside cell in the same four-cycle, consecutive to the first. A four-cycle cannot contain all three axis pairs of the outside triple, so exactly two of the three outside cells are dirty in this case, with the last clean.

If all three outside cells are clean, each has its own internal square and no edges to the other two. If instead two are dirty and linked, they each have their internal matching and exactly one cross neighbor per site. For the latter assertion, use their common split vertex on axis a. In W(T_a), each cell vertex is already adjacent to its one first-layer parent in the component. Cubic degree in that component of order twelve leaves exactly two neighbors within the two cells. One is its own-cell mate, so exactly one is in the other cell. The third outside cell is clean and isolated from these two, with its own internal square. In both cases, every one of the twelve outside support sites has exactly two neighbors within those twelve sites. Their signs have sum zero as shown above, so one of the two neighbors has the same sign and the other the opposite sign.

## A degree contradiction for the norm-28 cycle field

A site within a cycle cell has just one same-sign neighbor within its own cell (its mate). The only other cycle cell of the same sign has disjoint axes and contribution zero: its defect takes value −1 at this site, and hence its contact count is zero. There are no same-sign edges from a cycle cell to the twelve outside support sites, since any outside support site meets only the two cycle cells of the opposite sign. Therefore every site in the support of the cycle field has exactly one same-sign neighbor, both within the cycle cells and among the twelve outside sites. By Av=−4v it has exactly five opposite-sign neighbors.

Write P,N for the 14 positive and 14 negative sites. Each side induces a matching of seven edges. At any of the other 71 sites the eigen-equation gives an equal number h of neighbors of each sign. There are 14·(14−6)=112 contacts to P from these sites. The total common-neighbor incidence allowance across all unordered P-pairs is 2·choose(14,2)−7=175 (each adjacent pair has allowance one instead of two). No point in P contributes, since its internal degree is one. The sites in N contribute 14·choose(5,2)=140. Thus the 71 exterior sites satisfy
```
Σ h=112,    Σ choose(h,2)=35.
```
But choose(h,2)≥h−1 for every nonnegative integer h, giving the contradiction 35≥112−71=41.

The dirty split graph cannot be empty because a root with all 21 cells clean is partner-regular, excluded by [the partner-regular theorem](../../conway-99-involution/partner-regular-kg/README.md). Under the assumption that all its wing components have order at most twelve it would consequently contain a dirty cycle. We ruled out length six and have now contradicted length four. Thus at every root some wing component has order at least eighteen. A triangle can account for at most three of the 99 roots, proving the lower bound of 33 distinct triangles.

**Related general inequality.** For any signed-unit neutral norm-28 field, let e count edges in either same-sign side (these counts are equal by the eigen-equation), and let D be the sum over its support of choose(the same-sign degree,2). The exterior heights satisfy Σh=140−4e and Σchoose(h,2)=98−9e−D: each support site has opposite-sign degree four more than its same-sign degree, and the allowance of 182−e for positive pairs is split between the two support sides and the exterior. The same integer inequality gives 5e+D≤29, in particular e≤5. The cycle case above would have e=7.
