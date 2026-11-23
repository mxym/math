# Five anticomplete prisms force a saturated triangle

In a hypothetical strongly regular graph with parameters (99,14,1,2), every family of five pairwise anticomplete induced triangular prisms lies in a unique family of six. The six are exactly the six components of the wing of one triangle, so that triangle lies on six actual nine-site rook grids. In particular the triangle is uniquely determined by the original five prisms. This is rank-free and does not assert that five such prisms occur.

## Contact heights and the aligned-prism rule

Write D for the union of the five prisms. If P and Q are any two of them, the centered signed difference 1_P−1_Q has Rayleigh quotient 3, the largest centered eigenvalue of the graph, hence is a true +3 eigenvector. Thus every vertex outside D has the same number h of neighbours into each of the five prisms. Extend h by zero on D. The [anticomplete-shore calculation](anticomplete-cubic-shores.md) for one prism gives

    (A−3I)1_P=h,       Ah=12·1−4h,       Σh=66,       Σh²=72.

Since 5h≤14, the height layers are H of three vertices of height two, M of sixty vertices of height one, and Z of six vertices of height zero outside D. A site in D has three neighbours in D and eleven outside, none in Z, so Ah=12 forces exactly one neighbour in H. Thus the D-neighbour sets of different H sites are disjoint. For x in H put d(x)=|N(x)∩H|. Its ten D contacts leave four outside neighbours and Ah=4, giving

    |N(x)∩Z|=d(x),       |N(x)∩M|=4−2d(x).

Every H site sees a pair in each prism. The pair cannot be contained in a triangular face, since such an edge already has its unique triangle cap. Because the three H pairs partition the six sites of each prism, they are a matching between its two triangular faces. Compare this with the prism's own three vertical edges. Call a pair vertical if it is one of those three edges; otherwise it is skew. Call a prism aligned when all its H pairs are vertical. Its matching is a permutation on three objects, so a nonaligned prism has either two skew pairs (a transposition) or three (a three-cycle).

At x in H, a skew pair contains two nonadjacent D contacts. Each needs a distinct mate in the graph induced on N(x), which is a disjoint union of edges. No site in another prism is a possible mate (different prisms are anticomplete). Nor can a site in Z be a mate (Z is anticomplete to D), or a different H site (D sites have their unique H neighbour x). Thus two distinct M neighbours of x must mate the two skew contacts. The number of prisms skew at x is at most 2−d(x).

For the following arguments, a bundle is the two-site H contact pair in an individual prism. A site of M hits exactly one site of each prism, and the following rules apply.

1. If an M site w is adjacent to x in H, it cannot hit a vertical x-bundle. The edge from x to either vertex of that vertical pair already has the other vertex as its unique common neighbour.
2. In an aligned prism, if x and y in H are adjacent, an M neighbour w of x cannot hit the y-bundle. For a site v of the y-bundle, x and v are nonadjacent and already have two common neighbours: y and the x-bundle site in the same triangular face as v. Thus a neighbour w of x hitting v would be a third. With rule 1, this means every M neighbour of x hits the third H-bundle in any aligned prism.

## The three nontriangle shapes of H are impossible

If H is a path x−y−z, then no prism is skew at y, and at most one prism is skew at each endpoint. Thus there are at least four aligned prisms. No M vertex can be common to x,z, since in an aligned prism rule 2 from the edges xy,yz would require its unique prism hit in both the z- and the x-bundle. The endpoints have y as one common neighbour, have disjoint D contacts, and must therefore have their other common neighbour in Z. It is the sole Z neighbour of each endpoint. But N(y) has ten D sites, x,z and two Z sites, and x,z are nonadjacent and cannot mate to a D site. They would both require the same Z mate, impossible.

If H is a single edge xy and an isolated vertex z, the sum of the three skew budgets is four, so at least three prisms are aligned. The nonadjacent pair x,z has both its common neighbours in M: they have no common D or H site and z has no Z contacts. These are both M neighbours of x since it has exactly two. In an aligned prism each such neighbour must hit the z-bundle by rule 2, but it is adjacent to z and so rule 1 forbids that hit.

If H is independent, the skew budget total is six, so there are at least two aligned prisms. Each pair of H sites has exactly two common M neighbours, since there are no common D, H or Z neighbours. A site of M cannot meet all three H sites: in an aligned prism each of the three bundles would be forbidden by rule 1. For any pair x,y and a common M neighbour w, write z for the third H site. In each aligned prism w must hit the z-bundle. Thus w,z are nonadjacent, with at least one distinct common neighbour in each aligned prism. There can be at most two aligned prisms, or their common-neighbour bound would be exceeded.

Consequently exactly two prisms are aligned and the other three each have exactly two skew bundles (the total skew budget is six). Every H site takes part in exactly two of these three transpositions. The transpositions are therefore xy, xz, and yz once each. Take w common to x,y. It cannot hit the z-bundle in any nonaligned prism, because its two common neighbours with z in the aligned prisms already exhaust that pair's budget. In the xz-transposed prism it also cannot hit the vertical y-bundle by rule 1, so it hits the x-bundle and gives a common neighbour of x,w there. In the yz-transposed prism it similarly hits the y-bundle, giving a common neighbour of y,w. Finally in the xy-transposed prism it must hit the x- or y-bundle (not the z-bundle), giving a second common neighbour on one of the adjacent pairs xw,yw. This is impossible.

## The sixth prism and unique triangle

Thus H is a triangle. Each site of H has two neighbours in Z, yielding six incidences; any Z site has at most one H neighbour by the triangle's common-neighbour bounds. Therefore each of the six Z sites has exactly one H neighbour. At a Z site, Ah=12 and all fourteen neighbours are outside D. Compared to the baseline of height one, this forces two more neighbours in Z than in H, hence three in Z. The six-site induced cubic graph is a triangular prism: its 2-regular complement is a six-cycle or two triangles; the second gives K_(3,3), forbidden by the common-neighbour cap.

Every site of D and Z has exactly one H neighbour, and together they have 36 sites, so D∪Z is the entire wing of H. Its six pairwise anticomplete cubic parts are the six prism components. Any further prism anticomplete to all five original prisms must use six vertices of Z, hence must equal Z. The recovering triangle H is unique as the three sites of height two. A larger family of pairwise anticomplete prisms is impossible, either by this uniqueness or by the [36-site cap for anticomplete cubic shores](anticomplete-cubic-shores.md).

In particular, the number of unordered families of five pairwise anticomplete prisms is exactly six times the number of triangles with six prism wing components. Each such triangle gives six five-subsets, and the proof recovers it uniquely from any one of them. This concerns six-prism triangles, not every saturated triangle with larger wing components.
