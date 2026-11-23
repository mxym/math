# An anticomplete cubic 18-set also forces a prism to be good

In a hypothetical SRG(99,14,1,2), let P be an induced prism and C an anticomplete induced 18-set of minimum degree at least three. Then the three rung caps of P form a triangle H, and P∪C together with the 12 remaining anticomplete sites lies in the wing of H. Those remaining 12 sites induce a cubic graph, necessarily a union of whole wing components. The 18-site set need not have any prism component.

Together with [the analogous cubic 24-set theorem](prism-anticomplete-cubic24.md) and [the cubic-shore bound](anticomplete-cubic-shores.md), this implies that the 30-site anticomplete region of any bad prism has at most 12 vertices in cubic components. It does not eliminate bad prisms with a smaller cubic region. This extends the previous [equal-prism bound](../rook-array-exclusion/bad-prisms.md), without requiring C to be a union of prisms.

## Set-up and saturated M contacts

Use the height h=(A−3I)1_P and its fixed classes H of three rung caps (h=2), M of sixty vertices (h=1), F of thirty anticomplete vertices (h=0 outside P). They satisfy Ah=12·1−4h. By centered Rayleigh, C is cubic, and (A−3I)1_C=3h, so C is a union of components of G[F]. Put S=P∪C, and Z=F∖C of size 12. The induced S is cubic, it is anticomplete to Z, and every S vertex sees exactly one H vertex: its eleven neighbours outside S all have height one or two and sum to 12. Label each S vertex by its unique H neighbour.

Each M vertex has exactly four S contacts. Every label can occur at most twice among those contacts, and if an M vertex is adjacent to an H vertex then its label can occur at most once. Thus an M vertex cannot meet all three H vertices. An M vertex meeting two H has support label counts exactly (1,1,2), the 2 at its omitted H label. For such a vertex all three common-neighbour budgets with H are spent entirely on its S contacts. In particular all M vertices meeting two H are anticomplete to the set Z_H of Z vertices touching H.

For x in H with d_x neighbours in H, there are eight S neighbours and six neighbours outside S. Their required height sum is 4, hence

    |N(x)∩M|=4−2d_x,       |N(x)∩Z|=2+d_x.

A site z in Z with e neighbours in H has e+2 neighbours in Z and 12−2e neighbours in M: no S neighbours, and its total height sum is 12. No site of Z can meet all three H, because such a site has six M neighbours; any one of those would share this Z site with each H, leaving at most one S contact per H label, fewer than its required four.

## H cannot be a path or a single edge

If H is a path, the nine sites P∪H have the nine prism edges, six rung-cap edges and two H edges, for a total of 17, contrary to the published [nine-site grid density gap](../../conway-99-involution/grid-density-gap/README.md).

Suppose H has one edge xy and an isolated point z. No M vertex can meet two H in this shape. A vertex meeting x,y must have one S contact labeled x and also sees y, giving two common neighbours with the adjacent x. A vertex meeting x,z would have two S contacts labeled y and also see x, giving three common neighbours with the nonadjacent y. The possibility of meeting y,z is symmetric. Now the nonadjacent pairs x,z and y,z have no common neighbour in S,H,M, so each must have two in Z. Both Z neighbours of z would therefore see all three H, already shown impossible.

## The independent H case

Write Z_x=N(x)∩Z, a two-set, and k_xy=|Z_x∩Z_y| for distinct H vertices. No Z meets all three H, so for each x the sum u_x of its two k-values is at most two. The pair x,y has exactly 2−k_xy common M neighbours: its remaining common-neighbour slots are spent in Z and cannot appear in S or H. Thus x has exactly 4−u_x M neighbours that meet two H, and u_x M neighbours that meet only x.

If u_x≤1, then at least three of x's M neighbours meet two H. Each of these must mate an S site inside the perfect matching on N(x), since their adjacent pair with x has its unique common neighbour at an S site. The total number of S neighbours of x is eight, so the number unmatched inside S is even. Their only possible outside mates are in M: H is independent and Z anticomplete to S. Therefore all four M neighbours of x must mate S and the two Z neighbours must mate each other. In particular Z_x is an edge.

If some k_xy=2, then the third H point z has u_z=0, because no Z site sees all three H. All its M neighbours therefore meet two H and are anticomplete to Z_H, and its Z_z pair is an edge. Take a point v of Z_x=Z_y. The pair v,z has no common neighbour in S,H,M, so both sites of Z_z would be adjacent to v, giving a second triangle cap beside z on that edge. Thus all k-values are at most one.

Similarly u_x=0 is impossible: choose any point of another Z_y, which by the zero overlaps is not in Z_x. The same argument would make it adjacent to both endpoints of Z_x, whose edge already has cap x. Hence at least two k-values are positive.

If the positive overlaps form a path x−y−z, the two sets Z_x and Z_z are disjoint edges (since the endpoints have u=1). For either v∈Z_z, the nonadjacent pair x,v has no common neighbour in S or H, and at most one in Z_x because that edge already has cap x. Of x's M neighbours only its one neighbour meeting only x can see v, since the others are anticomplete to Z_H. This same M neighbour must therefore see both endpoints of the Z_z edge, giving a second cap beside z. Thus all three k-values are one.

Since no Z site meets all three H, the three pair intersections are distinct, and each Z_x consists of the two sites it shares with a different other H. If Z_x were not an edge, both its sites would need mates among x's M neighbours in the matching on N(x). Only the two M neighbours that meet only x can be mates, since the other two avoid Z_H. Such an M neighbour w would then have no S contact labeled x (its adjacent pair with x already has its unique common neighbour at that Z mate). It would have exactly two S contacts of each other label, leaving no further common-neighbour slot with either other H vertex. But its Z mate meets one of those other vertices and supplies a third common neighbour. Thus each Z_x is an edge. The three shared Z sites would form a triangle with each edge already having its own H cap, which is impossible. This finishes the independent case.

## H is a triangle

The only remaining H is a triangle. Its twelve incidences to Z must all go to different Z vertices, because no exterior vertex can see two sites of a triangle. Consequently every Z vertex has exactly one H neighbour and, by the formula above, exactly three neighbours in Z. The 36 vertices of S∪Z are precisely the wing of H, and the three cubic pieces P,C,Z split into full wing components. In particular the two triangular faces of P together with H form its unique rook grid. If the original prism were bad, its cubic-component volume could not be 18, 24 or 30 by the three cited cases; it is a multiple of six and thus at most twelve.
