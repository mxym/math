# Nongrid prism classes and a grid-sensitive prism bound

Let \(\Gamma\) be a strongly regular graph with parameters \((99,14,1,2)\). Let \(P\) be its number of induced triangular prisms, \(G\) its number of induced \(3\times3\) rook grids, and \(B=P-6G\). A prism is **good** if it lies in a rook grid, and **bad** otherwise. A good prism lies in exactly one grid: on each of its three matching edges take the unique common neighbor of the endpoints. These three caps must be the missing grid line. Thus \(B\) counts the bad prisms.

**Theorem.** Each graph-mark class of bad prisms contains at most three prisms, and
\[
  13P\le9240+20B.
\]
Consequently the primal norm-four shell satisfies \(y_2\ge462+2\lceil B/3\rceil\). If all prisms are good then \(P\le708\); at the existing upper limit \(P=851\), one must have \(B\ge95\) and \(y_2\ge526\). These are necessary conditions, not an exclusion of a Seidel rank or of the graph.

The multiplicity bound is analytic. The second inequality also uses the separate [unconditional exclusion of the nine-triangle rook array](README.md).

## Equal bad prisms

Use the marks \(u_i\) with Gram matrix \(C=3I-A+J/9\), and write \(w_S=\sum_{i\in S}u_i\). The [balanced-mass-six argument](../rank-34-short-support/README.md) proves that distinct prisms with the same mark are disjoint and anticomplete. Their common vector \((A-3I)1_X\) is zero on their sites. For one such prism \(X\), an outside vertex touches at most one site in each parallel triangle. Its three matching-edge caps are precisely the sites with two contacts: a nonedge between the parallel triangles already has two internal common neighbors. Counting the \(6(14-3)=66\) edges leaving \(X\) gives exactly 60 sites with one contact. The equal-mark identity shows that these are the **same** sets \(D\) (three double contacts) and \(U\) (60 single contacts) for every prism in the class. Let \(h\) be the class size and \(F\) the remaining sites, outside its \(6h\) prism sites and outside \(D,U\).

Every \(u\in U\) has one neighbor in each of the \(h\) prisms. Label each such neighbor by the cap \(d\in D\) on its rung. Any one cap occurs at most twice, because every occurrence is a different common neighbor of \(u,d\). Moreover, if \(u\) is adjacent to \(d\), then \(d\) does not occur at all: the edge between \(d\) and any such prism neighbor already has its unique common neighbor at the opposite rung endpoint.

For \(d\in D\), sum the common-neighbor counts with the six sites of one fixed prism. The sum is \(2\cdot1+4\cdot2=10\). Its two rung neighbors in that prism contribute six two-walks; neighbors in other class prisms contribute none; neighbors in \(U,D,F\) contribute respectively one, two, zero apiece. Thus
\[
 \deg_U(d)+2\deg_D(d)=4.
\]
If \(h\ge5\), every cap must occur in every \(u\)'s contact labels. Hence \(U\) has no edges to \(D\), so all three caps have internal degree two and the prism is good. Suppose then that a bad class has \(h=4\). Its cap triple has at most one edge: two edges would give a nine-set \(X\cup D\) with 17 edges, contrary to the [nine-site density gap](../../conway-99-involution/grid-density-gap/README.md); three would give a grid. Choose an isolated cap \(d\). No \(u\in U\) can see two caps, since all four of its prism contacts would then have the third label. The cap \(d\) has eight prism neighbors and four \(U\)-neighbors by the displayed identity, leaving exactly two in \(F\). Each other cap has two common neighbors with \(d\), neither in a prism (different rungs), nor in \(U\), nor in \(D\). Both of those \(F\)-neighbors therefore see all three caps. But for such an \(f\in F\), summing common neighbors to a fixed prism gives \(12=\deg_U(f)+2\deg_D(f)\), so \(f\) has six \(U\)-neighbors. A \(U\)-neighbor already shares \(f\) with each cap, and can therefore have at most one prism-contact of each of the three labels, impossible when \(h=4\). This proves \(h\le3\).

There are 462 distinct signed triangle marks of norm four; a prism mark has norm four and is a signed triangle mark only in the good case, by the [positive mass-nine equality argument](../rank-34-short-support/README.md). A positive prism mark has charge 6 and its negative has charge 3 modulo 9, so opposite signs of bad classes cannot coincide. This gives the asserted lower bound for \(y_2\).

## Rectangles of good prism mates

For a graph triangle \(T\), let \(p_T\) count its prism mates, and \(g_T\) its grids. Its good mates are the \(2g_T\) other parallel lines, paired by grid. Distinct triangles are either incident at one vertex (mark inner product zero), or disjoint with a matching of \(m\) cross-edges (inner product \(1-m\)). Every grid is one-dominating outside itself. Two mates obtained from different grids through \(T\) are disjoint and anticomplete: those grids already have their common line, and each vertex in either other parallel line uses its single contact into the opposite grid on \(T\). Distinct grids through \(T\) cannot share another vertex, since the neighbors of an outside vertex in a grid number one, or equivalently since the associated six-site wing components below are disjoint.

There are \(32-p_T\) triangles anticomplete to \(T\). For completeness the triangle marks sum to zero and their frame operator is \(21I\) on the 44-dimensional mark space: for site-triangle incidence \(M\), \(MM^t=7I+A\), while the site marks form a \(7I\) frame in the \(-4\) eigenspace. If \(a,c\) count the anticomplete and two-cross triangles at \(T\), the first and second moments against \(w_T\) give \(a-c-2p_T=-4\) and \(a+c+4p_T=68\). There are therefore \(3696-P\) unordered anticomplete triangle pairs.

Form the simple graph on all 231 triangles whose edges are good prism pairs. For an anticomplete pair let \(m\) be its number of common good mates, and let \(R\) be the number of unoriented four-cycles in this graph. A pair of mates of a single triangle in its *same* grid cannot have a second common mate: the two have inner product \(-2\), while two neighbors from different grids of any common mate have inner product \(+1\); in a single grid the third line of a given prism is unique. Thus each four-cycle has anticomplete opposite pairs. Counting length-two paths with anticomplete ends and using \(m\le1+\binom m2\) gives
\[
 \sum_T 2g_T(g_T-1)\ \le\ 3696-P+2R. \tag{1}
\]

In any such cycle name its opposite pairs \(A_1,A_2\) and \(C_1,C_2\). All four cross prisms are good. For each take its third parallel line \(K_{ij}\), with mark \(k_{ij}=-a_i-c_j\) (lower case denotes the corresponding mark). The eight triangles are disjoint: each \(K_{ij}\) meets its two original lines in a prism and is anticomplete to the other two by taking inner products. Distinct \(K\)'s are anticomplete if they share one index and are prism mates if both indices differ, again by inner products. In particular \(X=K_{11}\cup K_{22}\) and \(Y=K_{12}\cup K_{21}\) are distinct prisms of equal mark.

Both are bad. If either closes, its third triangle \(E\) has mark \(e=a_1+a_2+c_1+c_2\). It is anticomplete to the four original lines and is a prism mate of all four \(K\)'s, by their inner products. The other diagonal also closes to \(E\), since its two marks and \(e\) sum to zero, making the union a nine-site grid by the [equality case](../../conway-99-involution/grid-density-gap/README.md). The nine disjoint triangles would then form the excluded array, explicitly in rows
\[
 (A_1,C_1,K_{11}),\qquad (C_2,A_2,K_{22}),\qquad (K_{12},K_{21},E).
\]
Each row and column is one of the six literal grids; all other line pairs are anticomplete. This contradicts the [rook-array exclusion](README.md).

A face \(E\) of a bad prism has \(g_E\le4\). The 36 neighbors outside a root triangle fall into three 12-site wings according to which vertex they see. There is a perfect matching in each wing (the root's neighborhood is seven disjoint edges), and a perfect matching between each pair of wings (use the common-neighbor rule with the other root vertex). Thus the induced wing graph is cubic. Each grid through the root occupies an entire six-site prism component, with two sites in each wing. Five such components would leave just six vertices in a connected simple cubic graph, hence a prism or \(K_{3,3}\); the latter is impossible by the common-neighbor bound. In the prism case the two triangles have one point per wing: a same-wing edge already has its unique cap at the root. The other three edges are the within-wing matching, so this component supplies a sixth grid. Six grid components exhaust the wings and leave no bad mate.

Fix two different equal-mark bad prisms \(X,Y\), and a face \(E\) of \(X\) and \(K\) of \(Y\). A rectangle yielding \(X,Y\) determines one grid through \(E\), whose other parallel lines are a pair of the original four lines. This grid determines the rectangle uniquely. Indeed in a genuine lift exactly one of those two lines must be a prism mate of \(K\). At most one can be: \(K\) is anticomplete to \(E\) and lies wholly outside the grid (its vertices see no \(E\)), so every vertex of \(K\) has just one grid contact. Having identified that line, its unique grid with \(K\) gives a third original line, whose unique grid with the opposite face of \(X\) recovers the fourth. Hence at most \(g_E\le4\) rectangles yield \(X,Y\). Each rectangle charges one unordered equal-class pair, so
\[
 R\le4\sum_{\text{bad classes}}\binom h2\le4B
\]
by \(h\le3\). Finally \(g(g-1)\ge6g-12\) for every integer \(g\), \(\sum_Tg_T=6G=P-B\), and (1) imply
\[
 12(P-B)-5544\le3696-P+8B.
\]
This is the desired inequality. The numerical consequences use \(B\equiv P\pmod6\).
