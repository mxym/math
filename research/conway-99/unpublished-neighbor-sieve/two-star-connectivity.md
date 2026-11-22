# The twenty ordinary sites at every nonedge are connected

Let $p,y$ be any nonadjacent vertices of a graph with the Conway parameters. Write $a,b$ for their common neighbors and $X=N(p)\setminus\{a,b\}$, $Y=N(y)\setminus\{a,b\}$. The two mates of $a,b$ in each root neighborhood are the four marked sites. Deleting them from $X,Y$ gives ten ordinary sites $X_0,Y_0$ on each side. The induced graph on these twenty sites is connected. The full 28-site neighborhood spans exactly 26 dimensions of the 44-dimensional marked space.

## Counting sites outside the two neighborhoods

Each ordinary site has one mate on its own side, two neighbors across in $X$ or $Y$, and its root, for a total of four neighbors among the 28 sites. Each marked site has exactly one cross neighbor. The 71 remaining sites split into ten adjacent to $a$, ten adjacent to $b$, and 51 adjacent to neither. Indeed $a$ has four neighbors in the 28-site chart, and the only common neighbors of $a,b$ are $p,y$.

Consider any connected component $C$ of the induced ordinary graph. The mate edges give even numbers $x,y'$ of sites on its two sides. If there are $d_X,d_Y$ edges from these sides to opposite marked sites, the cross-edge count gives $2x-d_X=2y'-d_Y$. At most two opposite marked sites can be used from either side. Consequently $x=y'=n$ and $d_X=d_Y=d$. Put $s=2n$.

For a site $z$ outside the chart let $t_z=|N(z)\cap C|$. We have $\sum_z t_z=10s$. Write $A_C$ here for the adjacency on the entire 28-site chart and $c$ for the indicator of the component. The common-neighbor equation gives
$$\sum_z t_z^2=12s+2s^2-c^t A_C c-\|A_C c\|^2.$$
If $d=0$, the two terms subtracted are $3s$ and $2n^2+9s$. The square sum is $3s^2/2$. If $d=1$, two ordinary sites have internal degree two instead of three, and two marked sites have one neighbor each in $C$. The terms subtracted become $3s-2$ and $2n^2+9s-8$. The square sum is then $3s^2/2+10$.

On the twenty outside sites adjacent to $a$ or $b$ the sum of $t_z$ is $2s-2d$. For each ordinary site and either common neighbor, one common neighbor is its own root. Each edge from the ordinary site to a marked site accounts for one of the remaining common-neighbor requirements inside the chart. The sum on the other 51 outside sites is therefore $8s+2d$.

For $m$ nonnegative integers with sum $k$, the least possible square sum is attained by taking the entries as equal as possible. Applying this separately on the twenty and the 51 sites gives the following contradictions.

| Ordinary sites in component | Marked edges from each side | Forced sum of squares | Minimum on the two groups |
| ---: | ---: | ---: | ---: |
| 8 | 0 | 96 | 106 |
| 12 | 0 | 216 | 218 |
| 16 | 0 | 384 | 390 |
| 8 | 1 | 106 | 110 |

A component with two sites on each side and $d\le1$ would need at least three cross edges. Each side is a mate pair, whose common-neighbor allowance is already taken by its root, so the cross edges between them form a matching of size at most two. The table and this observation exclude all proper components with $d=0$. Every component in a disconnected ordinary graph must then consume at least one of the two available marked cross incidences on each side. There must be precisely two components, each with $d=1$. The smaller contains at most four of the ten ordinary sites on each side because their numbers are even. Both possible sizes have just been excluded.

## The 18-dimensional complement at a nonedge

On the 26 boundary sites obtained by deleting $p,y$ from the chart, let $D$ denote induced adjacency. Each ordinary site has degree three. The four marked sites and the two common neighbors have degree two. Thus $3I-D$ is the sum of the graph Laplacian and a nonnegative diagonal matrix supported on the six degree-two sites. Its kernel consists of the constant vectors on components having only degree-three sites. Connectivity on the twenty ordinary sites shows that there is at most one such component. Any nonzero vector in that kernel has nonzero total sum. Hence the boundary Gram $3I-D+J/9$ is positive definite. The neighbor equations at $p,y$ recover both omitted marks from the boundary. The span has dimension 26, leaving an 18-dimensional orthogonal complement at every nonedge.

As in the [triangle reconstruction](triangle-complement.md), once all contacts of the 71 exterior points with the 28-site chart are prescribed, seventeen independent exterior adjacency rows suffice. They leave a rank-one residual Gram, and the remaining sign products are determined or tested by rational comparisons. Two different completions at that stage would differ by rank at most two. The transposition lemma in the same reference requires twelve old neighbors to change at a pair of sites, whereas every exterior site has only ten or eleven old exterior neighbors. Existence of compatible contacts and rows is still open.
