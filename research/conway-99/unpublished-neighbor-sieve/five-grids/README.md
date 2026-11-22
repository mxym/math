# Five intersecting grids force an uncovered square

Let two distinct induced three-by-three rook grids meet in a triangle $L$. At each vertex $p$ of $L$, take the line perpendicular to $L$ in each grid, where a line is a three-vertex clique. If the two perpendiculars lie on a common rook grid at all three vertices of $L$, the Conway graph has an induced square outside every triangular prism. At least one corner of that square lies in the union of the three perpendicular grids.

Consequently, if all squares are covered, two grids on a triangle can have this extra grid at **at most two** of its three vertices. No saturation, symmetry or rank assumption is used. Without assuming coverage, the five grids already force a separate conclusion. The three perpendicular grids have exactly five triangles meeting all three, namely $L$ and the four parallel copies of $L$ in the two original grids.

## Coordinates on the 27 points

Any point outside a rook grid has exactly one neighbor in it. Every pair inside has its full common-neighbor count there, and the nine points send 90 edges to the 90 outside points. Two perpendicular lines at a point determine their entire grid by the second common neighbor of each pair of noncentral signed points. Hence distinct grids on $L$ intersect in exactly $L$. Each off-line point of one original grid has its contact with the other on $L$.

Write $B_0,B_1,B_2$ for the grids on perpendiculars at the three vertices of $L$. In each, use the central point, its two pairs of axial neighbors and the four corners. A corner sees a noncentral point of each original grid. Thus it belongs to neither original grid, and its unique contact with the first original grid identifies which $B_p$ it belongs to. This proves the three $B_p$ are disjoint. Between any two there is a perfect matching by the one-neighbor property. Relative to consistent labels in the original grids these matchings identify the centers and the four axial points. The three maps on the four remaining corners are free permutations before checking common neighbors, giving $24^3=13824$ tables.

Let $S$ be adjacency on these 27 points. Each remaining point sees one vertex in each $B_p$ and one in each of the two original grids. Its three contacts must therefore have one of two forms.

* A center in one grid and corners in the other two.
* An axial point of the first perpendicular direction in one grid, an axial point of the second direction in another, and a corner in the remaining grid.

Two points cannot have the same triple since then they would have three common neighbors. For each pair of contact positions $u,v$ in different grids, the required number of outside triples containing it is $2-S_{uv}-(S^2)_{uv}$. The two contacts determine which of the nine ordered groups the triple belongs to. When both are corners, its third contact is the unique possible center, so these pair counts determine all three center groups. Each has eight triples. In each of the six other groups, choose a binary two-by-two table for each of its four possible corners. The three two-coordinate margins are all prescribed. Enumerating these tables gives eight triples per group.

The [checker](verify.py) relabels the three grids simultaneously with their centers and uses the eight symmetries of the central cross. It compares each table with all 48 actions and uses its stabilizer to identify boundary choices. Exactly 53 normalized tables have feasible margins, in seven orbits. Each such shell has exactly 23 triangles, of which 18 belong to individual grids. This proves the assertion about five transversal triangles without any assumption on covered squares.

## Completing neighborhoods under the coverage assumption

Let $C$ be the binary $72$-by-$27$ contact matrix and $X$ the unknown exterior adjacency. The graph equation gives
$$XC=T=2J-C-CS,\qquad X^2+X=12I+2J-CC^t.$$
Thus two exterior points cannot be adjacent if they share two shell contacts, or if one contacts a column where the other has demand zero. Call the remaining exterior edges possible. Edges with a shell endpoint are known exactly.

At a shell point $p$, the triangles on its 14 neighbors determine a perfect matching. Each shell neighbor has a unique mate already determined by $S,C$. Enumerate all matchings on the remaining neighbors using possible edges. For each nonadjacent shell pair $p,q$, their common neighbors $r,s$ are known. Write $m_p$ and $m_q$ for proposed matchings. A prism over the square needs at least one of the opposite cap pairs $(m_p(r),m_q(s))$ and $(m_p(s),m_q(r))$ to form an edge. Delete a matching choice if it has no compatible choice at another shell point. Each deletion is necessary since a genuine edge must pass the possibility test.

For an exterior vertex $y$ enumerate its set $R_y$ of eleven exterior neighbors. Its contact sum must equal $T_y$. No two chosen neighbors can share two shell contacts because they also share $y$. Whenever a shell neighbor of $y$ requires an exterior mate, that mate must occur in a retained shell matching. The [neighborhood checker](neighborhoods.py) chooses a shell column of positive remaining demand and branches over all ways of meeting that demand. It makes no assumption about automorphisms of a completion and imposes no bound on the number of rows.

For each row, match all 14 neighbors of $y$. The three shell neighbors have known mates from the proposed row. Two other neighbors of $y$ can be mates only when they share no shell contact, since $y$ already completes their triangle. For every shell point $p$ nonadjacent to $y$ let $r,s$ be their two common neighbors. The square needs either $m_y(r)$ joined to a possible $m_p(s)$, or $m_y(s)$ joined to a possible $m_p(r)$. Enumerating perfect matchings of the free neighbors tests both possibilities. A real graph supplies such a matching and passes every square test.

| Corner maps, indexed from zero | Labeled tables | Boundary types | Empty shell-matching domain | Impossible exterior neighborhood | Incompatible exterior pair |
| --- | ---: | ---: | ---: | ---: | ---: |
| 7,7,23 | 6 | 12 | 5 | 6 | 1 |
| 7,9,18 | 12 | 10 | 10 | 0 | 0 |
| 9,9,9 | 12 | 36 | 36 | 0 | 0 |
| 9,9,23 | 12 | 220 | 220 | 0 | 0 |
| 9,18,9 | 4 | 16 | 16 | 0 | 0 |
| 10,10,23 | 6 | 3 | 3 | 0 | 0 |
| 23,23,23 | 1 | 1231 | 540 | 691 | 0 |

In one boundary every single exterior neighborhood tested separately has a choice. Two specified exterior vertices have just one possible row each after the matching tests. Those rows violate symmetry or $|R_i\cap R_j|+[j\in R_i]=2-(CC^t)_{ij}$. Thus none of the 1,528 boundary types extends under full coverage. Only squares with a corner among the 27 points needed coverage in this proof.

Run `python3 -B verify.py` with NumPy. The [witness indices](witnesses.json.gz) tell it which exterior vertex or pair to exhaust when shell matching alone does not suffice. The checker regenerates all tables, all possible contacts and all relevant neighborhoods using integer arithmetic.

## Counting the restriction at lines

At a point $p$, let $H_p$ have the seven incident triangles as vertices, joining two when their perpendicular directions span a grid. For a line $L$ through $p$, the neighbors of $L$ in $H_p$ are naturally the $g_L$ grids containing $L$. Write $e_p(L)$ for the number of edges among these neighbors. Under full coverage the result gives
$$\sum_{p\in L} e_p(L)\ \le\ 2\binom{g_L}{2}.$$
For example, if a triangle lies on six grids, at least fifteen of the 45 pairs of perpendicular directions counted over its three vertices must fail to span a grid. The inequality applies to each line separately. It leaves open the existence of both covered and uncovered Conway graphs.

The independent [signed matrix argument](complete-point-exclusion.md) excludes a point on all 21 grids. The [regular-cell argument](fifteen-grid-exclusion.md) bounds the number of grids at each point by fourteen.
