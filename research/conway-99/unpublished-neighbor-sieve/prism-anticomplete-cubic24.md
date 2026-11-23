# A prism and an anticomplete cubic 24-set complete a triangle wing

Let G be a hypothetical strongly regular graph with parameters (99,14,1,2), and let P be an induced triangular prism. Its 30-site anticomplete region F consists of the vertices outside P with no neighbour in P.

**Rank-free theorem.** Every induced subgraph N of minimum degree at least three that is anticomplete to and disjoint from P is a union of entire cubic components of G[F], each of size divisible by six. If |N|=24, the unique remaining six vertices of F form another prism R, and P,N,R together form the entire wing of a unique triangle H. In particular P and R are both good prisms in literal rook grids through H. N need not contain an induced prism and can be a connected 24-site component. By applying the assertion to all cubic components at once, a bad prism's anticomplete region has at most 18 vertices in cubic components.

This generalizes the five-prism phenomenon already implicit in [bad-prism class bounds](../rook-array-exclusion/bad-prisms.md), where every member of the volume-24 shore would have been a prism. It makes no claim that any such N exists.

## The fixed prism and its anticomplete region

Let h=(A−3I)1_P with A the adjacency matrix. It vanishes on P since P is cubic, and equals the number of contacts into P elsewhere. Each exterior vertex sees at most one point from each triangular face. A vertex that sees two must see the endpoints of a rung, since any nonedge across the two faces already has its two common neighbours inside the prism. Conversely each of the three rungs has an exterior cap, and the caps are distinct. Thus h=2 on three rung caps H, h=1 on sixty vertices M by the 66 total contacts, and h=0 on the remaining 30 exterior vertices F. Also Ah=12·1−4h from the strongly regular identity.

By the [centered Rayleigh argument](anticomplete-cubic-shores.md), any nonempty N as in the theorem is cubic, and the vector |N|1_P−6·1_N is a +3 eigenvector. Therefore

    (A−3I)1_N=(|N|/6)h.

Since some h=1, the integer |N| is divisible by six. It follows that every vertex of F outside N has no neighbour in N, so N is a union of entire components of G[F]. The same argument for each connected component (which is cubic and still anticomplete to P) shows its order is divisible by six. Conversely any union of cubic components of G[F] is anticomplete to P and satisfies the minimum-degree hypothesis.

## Twenty-four sites force the cap triangle

Suppose |N|=24. Put S=P∪N (30 sites) and Z=F∖N (six sites). The graph on S is cubic, and no site of S is adjacent to any site of Z. Every S vertex has exactly one neighbour in H: it has eleven neighbours outside S with heights one or two, whose required height sum is 12. Give each S vertex its unique H-neighbour as label. Every w in M has exactly five S contacts, one in P and four in N. Each label can occur on at most two of them, since each occurrence is a distinct common neighbour of w and that label's H vertex. If w is adjacent to a vertex of H, its label can occur at most once. Thus if w were adjacent to two H vertices it could have at most 1+1+2=4 S contacts. Hence no M vertex meets two H vertices.

For x in H, its ten S contacts leave four exterior neighbours in H∪M∪Z. Writing d=|N(x)∩H|, the required height sum 4 gives exactly d neighbours in Z and 4−2d in M.

* If the three caps H were independent, two of them would have no common neighbour in S (the labels are unique), in H, in M (proved above), or in Z (their Z degree would be zero). This is impossible.
* If H had just one edge, its isolated point and either endpoint would again have no common neighbour in any of these four classes.
* If H were a path x−y−z, the two endpoints would have one common neighbour y in H, none in S or M, and therefore one shared neighbour in Z, the sole Z neighbour of each. But the centre y has no M neighbours; its two nonadjacent neighbours x,z in H cannot be mated to any S neighbour of y, by uniqueness of the H label, and both would need the same Z mate in the matching on N(y). This is impossible.

Thus H is a triangle. Its six incidences to Z must be distributed one per Z vertex, since no exterior vertex meets two sites of a triangle. A site z∈Z has no S neighbours and its required height sum is 12, so compared to baseline height one it has two more Z neighbours than H neighbours. It therefore has three Z neighbours. A cubic induced graph on six vertices has complement C6 or two triangles; the second would give K_(3,3), with three common neighbours for a nonedge. Thus Z is a prism R.

Every site of S∪Z sees exactly one point of H, so these 36 sites are precisely H's wing. In it P and R are whole cubic components, and N is the union of the remaining components. The triangle is unique because its vertices were recovered as the three actual rung caps of P. Any prism disjoint and anticomplete to S is wholly in Z, so the new prism is also unique.

Finally a bad prism cannot have 24 vertices in cubic components of F by this theorem. It also cannot have all 30 vertices in cubic components: applying the maximum-size (6,30) case of the anticomplete-shore theorem makes the prism a component of a triangle wing, hence good. Since each component order is a multiple of six, the total for a bad prism is at most 18.

**Eighteen-site strengthening.** The [three-cap overlap argument](prism-anticomplete-cubic18.md) lowers the sufficient anticomplete cubic volume to eighteen even for a connected shore, and limits a bad prism's cubic anticomplete region to twelve sites.
