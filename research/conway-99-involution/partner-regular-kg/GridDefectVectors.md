# Real grid defects: at least 24 percolating partners at every vertex

**Theorem.** Every vertex of a hypothetical SRG(99,14,1,2) is contained in at most fifteen induced 3-by-3 rook grids and has **at least 24 distinct nonneighbors with which it 2-percolates**. This supersedes the local counts eight and sixteen in the simpler companion observations. It does not assert existence or nonexistence of the 99-graph, or exclude six or more missing grids at a root.

Use the signed-neighbor axes and four-point cells of [the partner-regular obstruction](README.md). For e=ab let S_e be the nine points consisting of the root o, the four neighbors on axes a,b, and the four exterior points of the cell C_e. Let m_e be the number of edges internal to C_e, and set

    v_e = (A−3I)1_{S_e} − 1.

As (A+4I)(A−3I)=2J and |S_e|=9, we have Av_e=−4v_e. The vector vanishes on o and on its first-layer neighbors: each axis parent in the set has its mate, the root and two cell neighbors, while a first-layer point outside sees exactly o. The exterior values, writing d_e(x) for the number of neighbors of x in C_e, are

    d_e(x)−2                 x in C_e,
    d_e(x)                   x in a different cell intersecting e,
    d_e(x)−1                 x in a cell disjoint from e.

The set S_e has 14+m_e internal edges (four root edges, two axis-pair edges and eight parent/label incidences, besides C_e). Since g=3I−A+J/9 obeys g²=7g and v_e=−g 1_{S_e},

    ||v_e||² = 7(27−2(14+m_e)+9) = 14(4−m_e).                 (1)

For x in C_ab, among its twelve exterior neighbors exactly two carry axis a: one sharing x's signed a-parent (by λ), and one carrying the opposite sign (the other common neighbor of x and that opposite parent, besides x's signed parent). The same holds for b. Thus d_e(x)≤2. If d_e(x)=2, both its required, distinct triangle partners through its two signed parents must be within C_e, since no further neighbor can carry either axis. They are the standard two sign flips. In particular v_e=0 iff all four points have both flips, i.e. iff C_e is clean. We call the other edges e dirty; there is at least one at every root, by the main theorem.

Let t_a indicate the signed neighbor pair of axis a. We have the *integer*, not just binary, identity

    sum_{e containing a} 1_{S_e} = (A+4I)(e_o+t_a).

Indeed A t_a=2e_o+t_a+sum_{e containing a}1_{C_e} and A e_o is the indicator of the full first layer. Multiplying by g, which annihilates A+4I, gives the equilibrium equations

    sum_{e containing a} v_e = 0  for every axis a.             (2)

Here g(A+4I)=0 follows from its definition and AJ=14J. Thus the dirty axis pairs carry nowhere-zero vector weights with *unsigned* star sums zero. Their underlying simple graph has no degree-one vertex. With at most five edges it is connected after removing isolated vertices (a nontrivial component needs at least three edges). A cycle with all degrees two must be even, since its weights alternate; the only possibility is a 4-cycle. Otherwise with ≤5 edges the only connected simple non-cycle of minimum degree two is the diamond K₄ minus an edge. In the diamond, the equations at its two degree-two vertices force opposite weights on both of their paths between the central vertices. Adding the central star equations gives twice the central edge weight zero, impossible. It remains to rule out the four-cycle.

## A four-dirty-cell cycle is impossible

Label its four dirty axis pairs cyclically e₁,…,e₄. The associated vectors alternate v,−v,v,−v and all have the same m_e=m. A clean cell C_h that uses an axis of the cycle has **no** edges to the other cells sharing that axis, by domination of its rook grid. In particular v vanishes there, by evaluating a dirty column sharing that axis with h. The only remaining clean cells on which v can be nonzero are the three pairs formed from the three axes outside the cycle. On these, all four dirty pairs are disjoint, so the values v and −v are both ≥−1. On a dirty cell itself, its own column is ≤0 (d_e≤2), and the opposite, disjoint dirty column has the same sign v_e and is ≥−1. Hence v has entries 0 or ±1 and is supported on at most 4·4+3·4=28 points. Equation (1) and nonzeroness force m=2 or 3.

*If m=3,* v has squared norm 14 and zero sum, so its support consists of seven positive and seven negative points. Each negative point has at least four positive neighbors by its eigen-equation, giving at least 7·binom(4,2)=42 common-neighbor incidences for pairs of positives. There are binom(7,2)=21 pairs each with at most two common neighbors, so no positive pair can have a common neighbor outside the negative support. The same holds with signs exchanged.

In each dirty four-cell, the degree into the cell is at least one (v_e≥−1) and at most two. With three internal edges it is a four-vertex path. Its degree-two vertices have both standard flips. Since every path edge touches one of these two vertices, the path is precisely the sign square with one flip deleted. The endpoints, which have the same nonzero value of v in this cell, share the signed parent along that missing flip. That parent is outside the support of v, contradicting the preceding pair bound.

*If m=2,* (1) forces the entire 28-point candidate support to be nonzero. On each dirty cell its own column equals −1 throughout, so each dirty cell is of one sign, two cells of each sign. Consider x in one of the three clean outside cells. All dirty cells are disjoint from its axes. For v(x)=1 we read from the four v_e formulas that x has two neighbors in each of the two negative dirty cells and zero in each of the two positive dirty cells; for v(x)=−1 interchange the signs. Their contribution already gives −4v(x). The only possible other neighbors of x in the support are its two neighbors on its own clean square, since the other two outside cells meet its own in an axis and clean intersecting cells have no edges between them. The two square-neighbor values must sum to zero. On a four-cycle this means opposite vertices have opposite signs; the sign pattern depends on exactly one of the two axis coordinates.

Each of these three clean squares therefore chooses one outside axis as its sign coordinate. At a signed first-layer point on an outside axis a, v vanishes, so the values on its neighbors sum to zero. Among supported cells these neighbors are the two labels of the specified sign in each of the two outside squares involving a. A square contributes zero if it does not choose a and ±2 if it does. Consequently a is chosen either zero times or twice. Summing over the three outside axes gives an even count, whereas the three squares made exactly three choices. This contradiction ends the four-cycle case.

Thus every root has at least six dirty cells. Each contains four nonneighbors generating the graph with the root by the closure classification in [the closure note](Percolation.md). In particular there are at least 1,188 unordered generating nonedges. This last aggregate estimate is not claimed sharp; the point of the theorem is the uniform 24 partners at each vertex.
