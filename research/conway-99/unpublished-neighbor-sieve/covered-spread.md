# A spread of saturated triangles in the grid-free covered branch

The [full-coverage theorem](saturated-choice.md) now forces a saturated triangle, allowing any number of grids.

Assume every square lies in a triangular prism. At any point on no three-by-three rook grid, exactly one incident triangle has twelve prism partners. Thus, if the entire graph is grid-free, its 99 points partition into 33 such triangles. This is an additional necessary condition on the [covered branch](covered-square.md).

## Ruling out a point with no saturated line

Call a triangle a line. At a point $o$ on no grid, its seven lines are signed axes. Each axis pair has a cell of four vertices labeled by their two signed parents. By the [covered-root theorem](../../conway-99-involution/uncovered-squares/covered-root/Theorem.md), two parallel flips join its four signs in a matching. Direct its edge $a\to b$ when the flips preserve the sign of $a$ and reverse that of $b$. This gives a tournament on the seven axes. An incoming cell at a line gives two prism partners of the line, one at each sign of the other axis. An outgoing cell gives none. Thus a line has twice its indegree in prism partners. A vertex of indegree six is unique when present.

For an arc $e$ write $S_e$ for its nine-site set consisting of $o$, the four signed parents and their cell. With $G=3I-A+J/9$ put $v_e=-G1_{S_e}$. We recall the properties used from the covered-root theorem. At $o$ and its neighbors the vectors vanish. At an exterior point $p$ in cell $i$,
$$w_e(p)=v_e(p)=|N(p)\cap C_e|-2[i=e]-[i,e\text{ disjoint}].$$
The entries are ternary. In its own cell the value is $-1$. For different arcs sharing their tail or their head the value is nonnegative. For arcs sharing an axis in opposite roles it is zero. For each axis, the column sums over the outgoing arcs and over the incoming arcs vanish separately. This follows by the axis sum identity and orthogonality between the two groups. In particular neither the indegree nor the outdegree can be one. The column Gram identity is
$$\langle v_i,v_j\rangle=-7\sum_{p\in C_i}w_j(p).$$
Indeed $G^2=7G$ and $v_j$ vanishes on the root and parents. These conditions at one point require no graph symmetry.

Suppose the point lacks a saturated line. The seven indegrees belong to $\{0,2,3,4\}$, with sum 21. Enumerate tournaments with a sorted score sequence, prescribing the directions from each successive vertex to the still-unprocessed ones and then removing relabelings within equal scores. This gives 96 diagrams.

For any diagram use the fourteen vanishing sums as equations on a row $w$. Reduce their coefficient matrix and express all entries in terms of free coordinates indexed by $F$. Thus $w=Dw_F$ for an explicit integer matrix $D$. Enumerate the ternary free coordinates and retain exactly the rows satisfying the pointwise restrictions in each possible cell. Let $n_{i,w}$ count such rows. Write $M_i=\sum_w n_{i,w}w$ for the vector of means without division by the cell size. Besides four rows per cell, the required homogeneous equations are
$$ M_{i,j}=\sum_{a\in F}D_{ia}M_{a,j}\quad (j\in F),\qquad
   \sum_{i,w} n_{i,w}\, w_jw_k=-7M_{j,k}\quad (j,k\in F).$$
The first follows because the matrix of cell sums is symmetric by the Gram identity and every row is a flow. The second is the Gram identity at the free coordinates.

For 94 diagrams these equations are already impossible. Each of the other two has an axis $a$ with six outgoing cells. In any such cell, an exterior vertex $y$ has precisely one neighbor outside the cell carrying the opposite $a$ sign. This neighbor $z$ belongs to a different cell with tail $a$: opposite-role links are forbidden and the signed-parent quotas fix the sign. Let $y',z'$ be their internal flip mates. The square on the two signs of $a$, $z$, and $y$ must be covered by a prism. The caps on the $a$-axis edge and on $yz$ cannot be adjacent: the former is $o$ and no signed parent is shared by $y,z$. The other caps $y',z'$ must therefore be adjacent. Thus the two points with a fixed $a$ sign in a cell go together to the opposite-sign pair in another cell. These links form a fixed-point-free permutation $\pi$ on the six cells, from their positive pairs to their negative pairs.

For two such cells $i,j$ put $c_{ij}=[\pi(i)=j]+[\pi(j)=i]$. There are exactly $2c_{ij}$ edges between them, so $M_{i,j}=2c_{ij}$. If $c_{ij}$ is zero or two then the individual entries in both cells are forced to zero or one respectively. All derangements on six letters give 130 distinct arrays $c$. The two remaining diagrams fail the equations for each of these 130 choices.

The [checker](covered_spread.py) reconstructs the tournaments, rows, equations and permutation arrays. For each system $Bx=d$ with $x\ge0$, the [integer certificate](covered-spread-cert.json.gz) either leaves a required cell empty or gives an integer row $u$ with $uB\le0$ and $ud>0$. No optimization solver is needed for replay. Running the checker with Python and NumPy verifies 94 direct cases and 260 permutation cases. Thus the required indegree-six line exists. The number of prism partners is a property of the line, so its other two points identify the same saturated line in the grid-free case. This proves the partition.

## A single saturated line also gives a spread

In any Conway graph a single saturated line $L$ already extends to a spread. Its twelve disjoint partner triangles partition the 36 wing sites. Each of the 60 far points sees six wing sites, two in each wing. No two of its six contacts are adjacent: within a wing their adjacency would give a second triangle on their edge, and every cross-wing edge already belongs to one of the partner triangles. In its matched neighborhood the six contacts must therefore be paired with six of its eight far neighbors. The other two far neighbors are mates. Every far point lies in exactly one triangle entirely among the 60 far points, so those triangles partition them into twenty triples. Together with $L$ and its twelve partners they give the spread. In particular, full coverage and even one point outside all grids are sufficient for the existence of a spread, allowing grids elsewhere.

## Quotient on 33 triangles

Write $N$ for the point-versus-spread-line incidence. Between any two distinct spread lines the edges form a matching, since a triangle edge already has its third vertex as a common neighbor. For a saturated line, every point in its three wings belongs to its unique prism partner there. If another spread line has two cross edges to the first, these two edges form opposite sides of a square. At either matching edge take its triangle and its moving labels: the two spread lines receive this triangle's direction at their respective roots and therefore both correspond to moving mate axes. The moving transfer matches whole axis pairs. As soon as one additional pair of labels is matched, both are, supplying the third cross edge. More explicitly, on a matching edge $pq$ with its cap $b$, the other two points of the spread line of $p$ form a mate pair in the $p$ wing of $pqb$. This pair belongs to the moving part because the line is the sink at $p$. The same holds for the other two points of the spread line at $q$. On moving labels the two wing mates coincide under the direct matching, by the [covered triangle description](covered-square.md). This excludes exactly two cross edges.

Let $H$ join spread lines linked by three edges and $S$ those linked by one. These are simple symmetric matrices on 33 sites with disjoint supports. If line $i$ has $d_i$ neighbors in $H$, it has $36-3d_i$ neighbors in $S$ and $2d_i-4$ spread lines with no cross edges. In particular $2\le d_i\le12$. The graph $H$ is triangle-free: two prism partners of a line correspond to different fixed labels, and three cross edges between them would require all three fixed-wing mate pairs to coincide, giving a grid.

To reconstruct, assign each singleton link to one of the three sites at each end. Each of the sites of line $i$ receives $12-d_i$ such links. Define $C_{xj}=1$ when $x$ is this endpoint of a singleton link to line $j$. Set $X=2I+H$ and $D=3H+S$. The exact constraints
$$N^tC=S,\qquad C^tC=30I-D+18J-3X^2-XS-SX$$
follow from $AN=NX+C$, $N^tN=3I$, and $A^2=12I-A+2J$. Thus even the pair intersections of the 33 singleton-contact columns are determined by the quotient.

Once these endpoint choices are made, the remaining unknowns are one permutation of three sites on each edge of $H$. With $B=NX+C$ their point-to-line equations are linear: $AB=12N-B+6J$. A completed adjacency must also satisfy $A^2+A=12I+2J$. Conversely any completed simple adjacency satisfying this identity directly supplies a Conway graph. Neither existence nor impossibility of the quotient completion is established here.

**Circulation marks.** The [mod-five description](saturated-five-currents.md) of a saturated triangle gives either a residual line or an explicit invisible integral circulation field. The [four-prism test](four-prism-five-flows.md) gives independent currents from any four prism components. These results do not assert that a saturated triangle is impossible.
