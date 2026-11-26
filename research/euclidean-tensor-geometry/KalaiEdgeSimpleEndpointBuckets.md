# Cube–simplex alternatives for edge-simple polytopes with controlled endpoint complexity

**Yongxian Zhang.** AI-assisted proof development; internal verification only, no priority claim.

Kalai's cube–simplex conjecture asks whether, for every fixed \(\ell,k\), sufficiently high dimensional convex polytopes must have an \(\ell\)-simplex face or a combinatorial \(k\)-cube face. We prove the full alternative for two overlapping subclasses of polytopes *simple in edges*, including polytopes with exponentially many nonsimple vertices and polytopes with no simple vertices. An edge is simple if it is in exactly \(d-1\) facets, equivalently its face figure is a \((d-2)\)-simplex. This is weaker than requiring every vertex to be simple.

We use [De Loera–Fang–Guo–Lu–Zheng, arXiv:2609.00397](https://arxiv.org/html/2609.00397v1), particularly Proposition 2.6 for the simplex direction blocks on a simple polytope and Theorem 2.2 for Blind–Blind's theorem; [Khovanskii's extension of Nikulin's bounds, as stated in Timorin, Theorem 2.7](https://arxiv.org/pdf/math/0010213#page=7) for flag ratios on edge-simple polytopes. The no-triangle case \(\ell=2\) for edge-simple polytopes was already an immediate corollary of those flag ratios and Blind–Blind; the point here is allowing triangles and using both endpoint figures together. Bounded primary-literature searches found no statement of the resulting endpoint-class estimate or defect thresholds. Neither the general edge-simple class nor unrestricted Kalai conjecture is settled here.

## 1. Endpoint blocks and triangular faces

Let \(P\) be an edge-simple \(d\)-polytope. For an edge \(e=uv\), let \(Q_u=P/u\) be the vertex figure at \(u\) and \(z_u\) its vertex corresponding to \(e\). Each vertex of \(Q_u\) has a simplex vertex figure: in the original polytope this is the figure of the edge through \(u\) corresponding to that vertex. Thus \(Q_u\) is simple. The same holds at \(v\).

For a vertex \(z\) of a simple polytope \(Q\), define a graph on its incident edge directions: connect two directions if their unique common 2-face at \(z\) is a triangle. Its connected components are cliques, including singleton directions, and a set of directions within one component determines a simplex face. This is the local statement in the proof of Proposition 2.6 of the paper cited above. For completeness, two intersecting pairs of triangular directions give adjacent triangular facets of the 3-face on the three directions. A simple 3-polytope with two such facets is a tetrahedron, so the third pair is joined. For a larger clique, use induction and the two \((r-1)\)-simplex facets obtained by omitting distinct directions from an \(r\)-element clique; they meet in an \((r-2)\)-simplex, and the \(r\)-face is itself a simplex. The geometric fact used in both arguments is this: if a full-dimensional \(r\)-simplex inside an \(r\)-polytope contains two vertices of the polytope that are simple there, and its edges at these vertices are all edges of the polytope, then the polytope equals the simplex. Each of the two tangent cones imposes nonnegativity of every barycentric coordinate except the coordinate of its own apex, so their intersection is exactly the simplex. For the two adjacent simplex facets, their union has \(r+1\) affinely independent vertices (the two distinct facet hyperplanes span the ambient space), and any two vertices of the intersection are simple and have exactly the simplex's \(r\) incident edge directions.

Let \(a_u(e)\) be the number of these clique blocks at \(z_u\) in \(Q_u\), and \(a_v(e)\) the analogous number. The \(d-1\) two-dimensional faces containing \(e\) are in bijection with the directions at \(z_u\), and also with those at \(z_v\). A triangular face through \(e\) therefore has an ordered pair of block labels.

Suppose \(t\) triangular faces \(uvx_1,\ldots,uvx_t\) through \(e\) share the same ordered pair. The \(t\) corresponding vertices in the simplex \(P/e\) span a \((t-1)\)-face, which lifts to a \((t+1)\)-face \(F\) of \(P\) containing these triangles. At \(u\), the \(t\) directions at \(z_u\) lie in one block, and thus span a simplex \(t\)-face of \(Q_u\). It lies in \(F/u\); by dimension \(t\) the two coincide. Consequently \(u\) is simple in \(F\), with incident edges to \(v,x_1,\ldots,x_t\). The analogous argument makes \(v\) simple in \(F\), with edges to \(u,x_1,\ldots,x_t\). These points form a full-dimensional simplex by independence of the \(t+1\) directions at \(u\). The two tangent cones prove \(F\) equals that simplex. If \(P\) has no \(\ell\)-simplex face, there cannot be \(t\ge\ell-1\) triangles in a single bucket, since a larger simplex contains an \(\ell\)-simplex face. This proves the edgewise bound
\[
\tau_2(e)\ \le\ \min\{d-1,(\ell-2)a_u(e)a_v(e)\}.
\tag{1}
\]
Here \(\tau_2(e)\) counts actual triangular 2-faces, not just 3-cycles of the polytope graph.

## 2. Exact inequalities and thresholds

Write \(f_i\) for the face counts, \(\tau_2\) for the number of triangular 2-faces, and \(c_k\) for the number of \(k\)-cube faces. Let
\[
L_\ell(P)=\frac{1}{f_1}\sum_{e=uv}
   \min\!\left\{1,\frac{(\ell-2)a_u(e)a_v(e)}{d-1}\right\}.
\]
If \(P\) is edge-simple with no \(\ell\)-simplex face, sum (1) over all edges and use the constant edge/2-face incidence \(f_{12}=(d-1)f_1\) to obtain
\[
\frac{\tau_2}{f_2}\le \frac{U_1(d,2)}{3}L_\ell(P).
\tag{2}
\]
Here for \(1\le i<j\le d/2\) the Khovanskii–Nikulin bound is \(f_{ij}/f_j\le U_i(d,j)\), where
\[
U_i(d,j)=\binom{d-i}{j-i}
\frac{\binom{\lfloor d/2\rfloor}{i}+\binom{\lceil d/2\rceil}{i}}
     {\binom{\lfloor d/2\rfloor}{j}+\binom{\lceil d/2\rceil}{j}}.
\]

For \(k=2\), if \(c_2=0\) then every nontriangular 2-face has at least five edges, and the mean edge count is at least \(5-2\tau_2/f_2\). Therefore \(U_1(d,2)(1+2L_\ell(P)/3)<5\) forces a quadrilateral.

For \(k\ge3\), let \(A_3=1\) and \(A_k=k-1\) for \(k\ge4\). Every noncube \(k\)-polytope \(F\) satisfies \(f_{k-1}(F)+A_k\tau_2(F)\ge2k+1\). If \(\tau_2(F)=0\), this is Blind–Blind including equality rigidity. If \(k\ge4\) and \(\tau_2(F)>0\), it follows from \(f_{k-1}(F)\ge k+2\) unless \(F\) is a simplex; for a simplex there are already at least two triangular faces. For \(k=3\), only four, five, or six facets need consideration: four means tetrahedron; six and noncube means at least one triangle by Blind–Blind. If it has five facets, Euler and degree at least three give \(f_0\le6\) and \(f_1\le9\), while \(2f_1\ge20-\tau_2(F)\), so \(\tau_2(F)\ge2\).

Every positive-dimensional face of an edge-simple polytope has a simplex upper face figure: fix an edge in the face and take an upper interval inside its simplex face figure. In particular each 2-face belongs to exactly \(\binom{d-2}{k-2}\) \(k\)-faces, so the mean number of triangular faces of a \(k\)-face is \((\tau_2/f_2)(f_{2k}/f_k)\). Counting facets of the \(k\)-faces and applying Khovanskii–Nikulin twice gives
\[
\frac{c_k}{f_k}\ \ge\
 2k+1-U_{k-1}(d,k)-\frac{A_k U_2(d,k)U_1(d,2)}{3}L_\ell(P)
 \qquad(d\ge 2k).
\tag{3}
\]

Consequently for every fixed \(\ell\ge3\), an edge-simple family of unbounded dimension satisfies the cube–simplex alternative for all sufficiently large member dimensions if
\[
\limsup_{d\to\infty} L_\ell(P)
 <\begin{cases}
 3/8,&k=2,\\[2pt]
 \dfrac{3}{4A_k\binom{k}{2}2^{k-2}},&k\ge3.
 \end{cases}
\]
Indeed \(U_i(d,k)\to\binom{k}{i}2^{k-i}\) and \(U_1(d,2)\to4\). In particular, for \(k=3\) the upper threshold is \(1/8\).

## 3. Two useful cases

* **Sparse edges with nonsimple endpoints.** Let \(\beta\) be the fraction of edges with at least one nonsimple endpoint. A globally simple vertex has simplex vertex figure, hence a single block for each incident edge. This yields \(L_\ell(P)\le\beta+(\ell-2)(1-\beta)/(d-1)\) for \(d\ge\ell\). Thus the above thresholds apply with \(\limsup\beta\) in place of \(\limsup L_\ell(P)\). If each vertex has at most \(c=o(d)\) nonsimple neighbors, then \(\beta\le c f_0/f_1\le2c/d=o(1)\), but a pointwise bound is not needed.
* **Few blocks in the endpoint figures.** If the average of \(a_u(e)a_v(e)\) over edges is \(o(d)\), then \(L_\ell(P)=o(1)\) for fixed \(\ell\), even if all vertices are nonsimple. For instance, if every vertex figure is a product of at most a fixed number of simplices, each of its edge-direction blocks at a vertex corresponds to a nontrivial factor. The hypersimplex \(\Delta(n,r)\) with \(2\le r\le n-2\) illustrates the latter condition (vertex figures \(\Delta_{r-1}\times\Delta_{n-r-1}\)); hypersimplices are already vertex-packing polytopes, so this example is not asserted as a new case by itself.

The first condition can allow exponentially many adjacent nonsimple vertices, with very high degree among them. For \(d\) a multiple of \(4\) and \(m=3d/4\), take
\[
P=[0,1]^d\cap\{\textstyle\sum_i x_i\le m\}.
\]
The cut hyperplane meets no cube edge in its interior, so the vertices are the retained \(0/1\)-vectors. Edges outside the cut facet are inherited cube edges; edges in the cut facet exchange one \(0\) and one \(1\) (any face with \(r\) coordinates free in this slice has dimension \(r-1\) if it has a relative-interior point with all those coordinates strictly between \(0\) and \(1\)). The inherited edges each have \(d-1\) coordinate facets; the exchanged edges have \(d-2\) coordinate facets and the cut facet. All indicated inequalities are facets for \(1<m<d\). The nonsimple vertices are the entire weight-\(m\) layer, of size \(\binom dm\ge4^{d/4}\) (choose one zero from each block of four); each has degree \(m+m(d-m)>d\). There are at least \(d2^{d-2}\) inherited cube edges by counting incidences with vertices of weight at most \(d/2\). At most \(d^2\binom dm\) edges touch the top layer, and \(\binom dm/2^d\le(2/3^{3/4})^d\) by applying the binomial generating function at \(3\). Thus \(\beta\to0\) in this genuinely nonsimple example, although it has large cube faces directly.

## 4. Concrete tetrahedron alternatives

For \(\ell=3\) and \(\beta\le1/16\), every edge-simple polytope of dimension \(d\ge47\) contains a tetrahedral or a cubical 3-face. Set \(m=\lceil d/2\rceil\). In (3), \(U_2(d,3)=6(m-1)/(m-2)\), \(U_1(d,2)=2(2m-1)/(m-1)\), and \(L_3/3\le1/48+(15/16)/(3(d-1))\). For \(m\ge24\), the upper bound for the subtracted terms is largest at \(m=24,d=47\), where it is \(69/11+(282/11)(61/2208)<7\). The factors decrease with \(m\), taking \(d\ge2m-1\).

For \(\ell=3\) and \(\beta\le3/16\), every edge-simple polytope of dimension \(d\ge17\) has a tetrahedral 3-face or a quadrilateral 2-face. The bound for \(U_1(d,2)(1+2L_3/3)\) is largest at \(m=9,d=17\), where it is \((17/4)(1+61/384)<5\).
