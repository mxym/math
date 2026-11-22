# Choosing among 3,467 exterior starting rows

Every Conway graph has a choice of triangle, first wing and exterior root giving one of 3,467 specified [first-row orbits](one-wing.md). This uses two double counts over all 4,158 unordered nonedges. No ranks or automorphisms enter. A discarded starting row can still occur at another choice of root in the same graph.

## Two local counts

Let $p,y$ be nonadjacent, let $a,b$ be their two common neighbors, and put $X=N(p)\setminus\{a,b\}$, $Y=N(y)\setminus\{a,b\}$. In the bipartite graph between $X$ and $Y$ there are two degree-one vertices on each side, the mates of $a,b$ in that root's neighborhood. All other vertices have degree two. Write $h$ for the number of edges directly between degree-one vertices and $l$ for the number of length-two paths whose two ends have degree one. These are unoriented counts.

Exactly five triangles through $p$ avoid every neighbor of $y$. They arise by taking any of the five ordinary mate pairs $q,r$ in $X$. The reverse direction gives five more. For each of these ten choices write $e$ for the number of edges among the exterior root's six contacts on the wings and $m$ for the number of repeated labels in its four contacts on the two missing wings. Thus $m$ is four minus the number of distinct first-wing labels on those four contacts. Write $E,M$ for the respective sums over the ten choices. All these numbers can be read from the induced 28-site graph on the two roots and their neighborhoods.

Let $P$ count the induced triangular prisms and $N=4158$. Each prism has three square faces and each face gives one edge between marked vertices for either diagonal. Conversely such a marked edge specifies the two matched triangle edges and their caps and so determines that prism direction. Therefore $\sum h=6P$. The earlier triangle count gives $\sum_y e_y=36-3t$ for a fixed triangle. Each prism is counted at each of its two triangles by $t$. There are 231 triangles and three choices of first wing. Consequently
$$\sum_{\{p,y\}} (E+3h)=6N.$$

For fixed triangle and first wing, there are $12-t$ nonadjacent pairs $Q_i,R_i$. Each already has common neighbor $P_i$. Its other common neighbor contributes exactly one to the sum of $m$ if it lies in the exterior. Otherwise it belongs to the $Q$ or $R$ wing. The total number of these latter possibilities over all triangles and first wings is $2\sum l$.

To verify the factor two, consider the case where the other common neighbor $z$ lies in the $Q$ wing. Center a two-star at the nonadjacent pair consisting of the $Q$ parent and $w=P_i$. Their common neighbors are the first parent and $Q_i$. In the $Q$ parent's neighborhood, the two marked mates are the $R$ parent and $z$. They connect across the two-star to the same vertex $R_i$ on the side of $w$, giving one marked length-two path. The case with $z$ in the $R$ wing exchanges their names. Conversely, for such a path pick which of the two common neighbors is the first parent. Its mate on the path-end side becomes the third parent and the root on that side is the second parent. The other common neighbor, its mate, the center of the path, and the opposite root recover $Q_i,z,R_i,w$ respectively. Both choices work. This account treats the last two wings as unordered. Thus
$$\sum_{\{p,y\}} (M+2l+h)=2N.$$

Some nonedge has $E+M+2l+4h\le8$. At least two of its ten triangle choices have $e=m=0$. Each has a normalized first row among the 6,727 base cases. The six labels are distinct since $e=0$ also prevents overlap with the root's first-wing contacts.

## Checking a covering list

Start with any such row at a nonedge and temporarily number the three parents, the twelve first-wing sites, the four additional contacts, the exterior root, and its eight exterior neighbors. These are exactly the 28 sites of the two-star. Choose two of the four contacts for each missing wing, up to exchanging those wings. In the exterior root's neighborhood, two exterior neighbors already pair with its first-wing contacts. The other four contacts must pair with four distinct vertices among the six remaining exterior neighbors. The last two pair with each other. All adjacencies in the 28-site graph are fixed by these choices, since both root neighborhoods induce matchings and every site outside the first root's neighborhood has its two neighbors in that neighborhood specified. Remove charts exceeding a common-neighbor quota.

For each chart with $E+M+2l+4h\le8$, consider the set of first-row orbits furnished by its choices with $e=m=0$. A list intersecting every such set suffices for a global starting search. The [stored list](two_star_cover.hex) contains 3,467 orbit indices in the deterministic order of the [first-row generator](one_wing_seeds.py). It was obtained by covering one-element choice sets first, repeatedly taking an orbit hitting the most outstanding sets, and deleting redundant selections. Minimality is not needed.

A separate [checker](two_star_cover.cpp) expands the selected rows under the 768 permitted first-wing relabelings. It enumerates charts starting at all 3,260 omitted rows and checks that each chart satisfying the bound has a selected view at one of its two roots. It computes $h,l$ directly in the bipartite graph and tests membership by the eight edges of a row; their degrees determine the four extra labels. The handoff between the [driver](two_star_cover.py) and the C++ checker is plain text. From this directory run

```sh
c++ -O3 -std=c++20 two_star_cover.cpp -o /tmp/conway-cover
python3 -B two_star_cover.py /tmp/conway-cover
```

This verifies that one may choose the first row from the list of 3,467. The other rows of the exterior remain undetermined.
