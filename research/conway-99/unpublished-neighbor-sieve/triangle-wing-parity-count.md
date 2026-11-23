# A weighted count of large triangle-wing components

For a triangle T of a hypothetical SRG(99,14,1,2), let W(T) be the cubic graph induced by the 36 vertices adjoining exactly one vertex of T. Write b₁₈ for the number of literal triangles whose largest wing component has order exactly 18, and b₂₄ for the number whose largest wing component has order at least 24.

**Theorem.** b₁₈+2b₂₄≥66. In fact, at every vertex with no incident triangle having a wing component of order at least 24, there are at least two distinct incident triangles with an 18-site component. If no triangle has any wing component of order at least 24, at least 66 triangles have an 18-site component. There is no assumption about the Seidel rank.

Use the [split-axis construction and large-component theorem](big-triangle-wing.md). At a root o the seven axes are the matched pairs in its neighborhood, one per triangle through o. Each component of a triangle's wing graph has size 6k and corresponds to a subset of k of the other axes. Split its axis into one vertex per such subset. Each original axis pair e becomes one edge of the resulting simple split graph, and any split vertex has degree k. Its incident real cell defects v_e sum to zero. At an axis pair e, if v_e=0 its cell is a clean grid and the edge joins two degree-one split vertices; conversely each degree-one split vertex is from such a clean cell. Removing the clean edges and their endpoints leaves the dirty split graph, with each retained v_e nonzero.

Suppose no triangle through o has a component of order at least 24. Every dirty split vertex then has degree two or three. By the preceding theorem at least one of them has degree three, and the number of degree-three vertices is even by the handshake identity. An original axis has at most two degree-three split vertices, since its component subsets partition just six axes. If there are four or more degree-three split vertices, at least two different original axes therefore have one.

It remains to consider exactly two degree-three split vertices. They must be in the same connected component of the dirty split graph: each connected component has an even number of odd-degree vertices, even if many other components or isolated clean pairs exist. Take a simple path between the two distinguished vertices. Every interior split vertex on this path has degree two, so the signed relation at it is v_e+v_f=0 for consecutive path edges. The first and last edge defects therefore agree up to an overall sign.

If the distinguished vertices had the same original axis a, the first and last edge labels would be distinct, both incident with a, and their cells would belong to different components of W(T_a). In particular they would have no edges to each other in the original graph. On the last cell the first defect is therefore identically zero: for different cells sharing an axis, that defect is precisely the contact count into its own cell. But the last defect is nonzero somewhere on its own cell: its own-cell value is degree minus two, and having degree two everywhere would make it clean. This contradicts the equality up to sign. Thus the two degree-three vertices belong to different original axes, proving the local claim.

Let R be the number of vertices incident with at least one triangle counted by b₂₄. One has R≤3b₂₄. The other 99−R vertices are incident with at least two triangles counted by b₁₈, and the R vertices each have at least one incident triangle from the union of the two populations. Counting incidences therefore gives
```
3(b₁₈+b₂₄) ≥ 2(99−R)+R = 198−R ≥ 198−3b₂₄.
```
This proves the claimed inequality. No compatibility or disjointness of the different triangles has been assumed.
