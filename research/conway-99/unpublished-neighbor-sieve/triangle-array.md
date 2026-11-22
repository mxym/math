# Nine triangles arranged in six rook grids

Let nine pairwise disjoint triangles be indexed by the nine positions of a three-by-three square. Suppose the union of the three triangles in each row and in each column induces a nine-point rook graph. Call the individual triangles fibers. The following restrictions apply.

1. In any Conway graph, the array has no choice of one point per fiber inducing a seventh rook graph with the same rows and columns.
2. Every such array forces an induced square outside all triangular prisms. Two opposite vertices of that square lie in array fibers in different rows and columns. In particular, the array is impossible if every square is covered.

These are local obstructions. A [saturated triangle](saturated-choice.md) alone supplies a partition into triangles. It does not by itself supply the six grids of the theorem.

## Common-neighbor counts

In a nine-point rook graph an adjacent pair has one common neighbor and a nonadjacent pair has two. An exterior point therefore has at most one neighbor in the grid. The nine grid points send a total of 90 edges to the 90 other points, so each outside point has exactly one neighbor there.

Between adjacent fiber positions the three edges form a matching, and the three matchings on any base line compose to the identity. There are no edges between opposite fiber positions (different row and column), since a point already meets the other row grid once along its column. The 72 points outside the 27-point array therefore have three contacts each, one in each row and column. The fiber positions of those contacts constitute one of six permutation transversals. The three contacts identify the exterior point uniquely, since two points cannot have three common neighbors.

For two opposite fibers, two paths in the base give the possible common neighbors inside the array. If their composed label permutations are $U,V$, the count of common neighbors still required for labels $i,j$ is
$$d_{ij}=2-[U(i)=j]-[V(i)=j].$$
All such neighbors select the unique third fiber that completes the transversal. The sum over $i,j$ equals twelve. On every transversal we need twelve distinct triples of labels with these exact pair counts on all three pairs of fibers.

## Excluding a section by parity

Suppose the nine chosen points form the additional rook graph. Call its selected label 0 in each fiber and name the other two labels $+$ and $-$. The matching on every base edge preserves 0 and either preserves or reverses the signs. The product around each base line preserves them.

On a transversal with positions $p,q,r$, fix any signed point at $p$. With the point labeled 0 at $r$ it has no common neighbor in the array, since both path permutations preserve 0. The two exterior common neighbors must select two different labels at $q$, by uniqueness of triples. They must both select signs, since an outside point has just one contact in the additional grid. Thus for every signed pair at $p,q$ there is exactly one exterior common neighbor with 0 at $r$. Every exterior common neighbor of that pair must have its 0 at $r$, so the pair has exactly one common neighbor inside the array as well.

Consequently the two paths between opposite positions act differently on signs. Every rectangle of the base must reverse signs around its boundary. Choose two rows and take the three rectangles obtained by choosing any two of the three columns. Multiplying their sign changes counts every vertical edge twice and the two horizontal base lines once each. The product is positive, contradicting the three negative rectangle products.

## Excluding every array under full square coverage

Normalize the fibers along the two edges from the first to the other rows in column one and the six edges from the first cell to the other cells in each row. These eight edges form a tree. The only free maps are now from the first row to the other two rows in each of the two remaining columns. There are $6^4=1296$ tables. Row and column permutations, transposition, and an initial permutation of the three labels give all relabelings needed below. The [checker](triangle_array.py) explicitly forms their orbits and enumerates the binary three-dimensional tables with the prescribed pair marginals.

| Free permutation indices | Number of labeled normalized tables | Boundary choices up to relabeling | Uncovered squares inside the array |
| --- | ---: | ---: | ---: |
| 0,1,2,3 | 108 | 2 | 3 |
| 0,1,3,2 | 216 | 21 | 4 |
| 1,2,2,1 | 54 | 51 | 4 |
| 1,2,3,5 | 36 | 6 | 6 |
| 3,4,4,3 | 2 | 6 | 0 |

Permutations of the three labels are indexed from zero in lexicographic order. The other normalized tables have an impossible marginal triple. Each edge in the array already lies on a unique triangle entirely inside the array. Call the third vertex the cap of the edge. A square is covered by a prism exactly when the caps for some pair of opposite edges are adjacent. Consequently all entries of the last column are determined inside the array.

For the six remaining boundaries let $S$ be the adjacency matrix of the 27-point array and $C$ the binary $72$-by-$27$ contact matrix. Let $X$ denote the unknown exterior adjacency. The matrix identity for a Conway graph implies
$$XC=T=2J-C-CS,\qquad X^2+X=12I+2J-CC^t.$$
Two exterior points with two common contacts cannot be adjacent. Nor can $y,z$ be adjacent if $z$ contacts $p$ and $T_{yp}=0$, or vice versa.

At an array point $p$ its six neighbors inside the array are already paired by their triangles through $p$. Its other eight neighbors must form a matching using allowed exterior edges. Enumerate all their perfect matchings. Write $m_p(y)$ for the proposed mate of exterior point $y$ at $p$. Two nonadjacent array points $p,q$ impose the following tests.

* If their common neighbors are an array point $r$ and an exterior point $y$, coverage of the square requires that $m_p(y)$ contacts the cap of $rq$, or that $m_q(y)$ contacts the cap of $rp$.
* If their two common neighbors $y,z$ are exterior, then one of the exterior pairs $(m_p(y),m_q(z))$ and $(m_p(z),m_q(y))$ must be adjacent. As a necessary test, at least one pair must consist of different points with fewer than two common array contacts.

Repeatedly delete a matching choice if it has no compatible choice at another array point. Five boundaries lose all possibilities at a point. In the sixth boundary exactly four matchings remain at each array point.

For each exterior $y$, enumerate all possible sets $R_y$ of its eleven exterior neighbors. Its incidence sum must give row $T_y$. Any two chosen neighbors with two common array contacts would also share $y$, so cannot both be selected. For each of the three array contacts of $y$ its mate must be among the surviving matching possibilities there. The search chooses an array point with positive remaining demand, branches over all subsets of its currently available neighbors of that size, and decrements their other demands. This leaves 33 sets at each of 54 points and 312 sets at each of 18 points. For each pair of exterior points $y,z$, the sets must satisfy
$$[z\in R_y]=[y\in R_z],\qquad |R_y\cap R_z|+[z\in R_y]=2-(CC^t)_{yz}.$$
Deleting choices without a compatible partner gives an empty domain in the first sweep. This excludes the last boundary. The only coverage tests in the argument concern squares with an opposite pair in the array. If two such vertices are in the same base row or column, the rook grid on that line supplies their full square and covers it. The uncovered square can therefore be chosen with its opposite vertices in fibers in different rows and columns.

Run `python3 triangle_array.py` with NumPy installed. The checker regenerates every table and boundary and uses exact arithmetic throughout.
