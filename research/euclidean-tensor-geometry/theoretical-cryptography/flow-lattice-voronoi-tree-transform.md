# Flow-lattice Voronoi moments from a directed tree determinant

Take a finite connected loopless multigraph with an arbitrary reference orientation and positive edge weights \(w_e\). Its integral flow lattice is \(\ker B\cap\mathbb Z^E\), where the incidence column \(b_e\) for edge \(i\to j\) is \(e_i-e_j\), and the squared norm is \(\sum_e w_e z_e^2\). Realize it in ordinary Euclidean space by \(y_e=\sqrt{w_e}z_e\). Let \(P\) be orthogonal projection to its real span, \(g_e=P(\sqrt{w_e}e_e)\), and \(X\) a uniform point in its Voronoi cell. Write \(c_e=1/w_e\), \(a_e=u\cdot g_e\) for a direction \(u\) in that span, and
\[
S(a)=\frac{\sinh(a/2)}{a/2},\qquad S(0)=1.
\]

**Theorem (moment generating determinant).** Give each edge \(i\to j\) two arcs with weights
\[
\beta_{ij,e}(u)=c_e\,\frac{e^{-a_e/2}}{S(a_e)}=\frac{c_e a_e}{e^{a_e}-1},
\qquad
\beta_{ji,e}(u)=c_e\,\frac{e^{a_e/2}}{S(a_e)}=\frac{c_e a_e}{1-e^{-a_e}}.
\]
Use their continuous values \(c_e\) at zero. Let \(A_r(u)\) be the minor of the resulting out-degree Laplacian, deleting row and column \(r\). For every real \(u\) in the flow space,
\[
\mathbb E e^{u\cdot X}
=\left(\prod_e S(a_e)\right)\frac{\det A_r(u)}{\det A_r(0)}.
\tag{1}
\]
Thus all directional and mixed moments follow from a determinant on vertices, rather than enumerating the Voronoi faces. The tilted directed graph is balanced, so the cofactor does not depend on \(r\).

In particular, let \(R_e\) be the effective resistance of \(e\) in the conductance network \(c_e\), put \(A=A_r(0)\), and, in the root-deleted coordinates, define
\[
K(u)=\tfrac12\sum_{e:i\to j} c_e a_e(e_i e_j^\top-e_j e_i^\top),
\]
where the vector of the deleted root is zero. The variance is exactly
\[
\operatorname{Var}(u\cdot X)=\frac1{12}\sum_e a_e^2+
\frac16\sum_e c_e R_e a_e^2+
\|A^{-1/2}K(u)A^{-1/2}\|_{\rm F}^2.
\tag{2}
\]
Moreover \(\mathbb E e^{u\cdot X}>\prod_e S(a_e)\) for every nonzero \(u\); the latter is the moment generating function of the orthogonal projection of a uniform point of the ambient weighted box. The projected uniform box and the uniform point of its projection are different laws. In particular the true Voronoi covariance exceeds that of the projected uniform box in every nonzero direction.

## 1. Projecting the box and selecting a tree face

The Voronoi cell is the projection of the weighted box \(\prod_e[-\sqrt{w_e}/2,\sqrt{w_e}/2]\). For an integral flow \(z\), its projected support inequality is at most \(\tfrac12\sum_e w_e|z_e|\le\tfrac12\sum_e w_e z_e^2\). Conversely a real flow has a conformal decomposition into positively weighted simple directed cycles: direct the edges according to the signs, follow edges until finding a cycle, subtract its smallest remaining flow, and repeat. The cycle Voronoi inequalities are the weighted support inequalities on those \(0,\pm1\) cycle vectors. Summing the conformal decomposition gives the projected-box support inequality for every real flow, proving equality.

We work in the original coordinates \(z_e\in[-1/2,1/2]\). With \(D_w=\operatorname{diag}(w_e)\), the fiber over a point of the projected box has the form \(z_0+D_w^{-1}B^\top p\), subject to the box constraints, with vertex potential \(p\) taken modulo constants. Fix a vertex \(r\) and a demand \(d\) summing to zero with \(d_i>0\) for every \(i\ne r\), and minimize \(d^\top p\) over each fiber. At an optimal vertex the active box constraints include an incidence basis, hence a spanning tree. They are exactly a spanning tree outside the projections of the faces fixing more than \(|V|-1\) coordinates, a volume-zero set. Such an optimal vertex exists because the potential polytope modulo constants is nonempty and bounded: each edge bounds a potential difference and the graph is connected.

For a spanning tree \(T\), solve \(B_T f=d\). Each tree edge's signed current \(f_e\) is nonzero, since deletion cuts off a component not containing \(r\), with strictly positive sum of demands. Its sign is \(s_{r,T}(e)=+1\) if the reference orientation points toward \(r\) in the tree and \(-1\) otherwise. On the fiber the objective, up to a constant, is \(\sum_{e\in T} f_e w_e z_e\). Thus the face minimizing term by term has \(z_e=-s_{r,T}(e)/2\) for all \(e\in T\). At a nondegenerate optimal vertex these are precisely its signs, because the tree incidence basis permits a local movement of any single active coordinate toward the interior with the other active coordinates unchanged. Conversely any point of this prescribed face is a unique minimizer in its fiber, as the distinct tree potentials are determined by these fixed coordinates. The images of these tree faces therefore tile the Voronoi cell up to null sets. All non-tree coordinates remain independently in their intervals on the given face.

## 2. Volumes and the matrix-tree formula

For an integral flow basis matrix \(F\) in the original coordinates, restriction to the non-tree edges of any spanning tree is an integer isomorphism: specifying their flows determines an integer tree flow by the reduced incidence matrix of that tree. If a complement of \(|V|-1\) edges is not a spanning tree, it contains a cycle and the analogous restriction has a kernel. Thus maximal minors of \(F\) are \(\pm1\) at spanning-tree complements and zero elsewhere. The squared covolume is
\[
\det(F^\top D_w F)=\sum_T \prod_{e\notin T} w_e
=\left(\prod_e w_e\right)\sum_T\prod_{e\in T}c_e
\]
by Cauchy–Binet. In orthonormal coordinates of the flow space the projected generators are the row vectors of \(D_w F(F^\top D_w F)^{-1/2}\). Hence the tile indexed by \(T\) has volume \(\prod_{e\notin T}w_e/\sqrt{\det(F^\top D_w F)}\), and its probability under uniform volume is proportional to \(\prod_{e\in T} c_e\).

Conditional on that tile, the direction \(u\) sees a centroid contribution \(-\sum_{e\in T}s_{r,T}(e)a_e/2\) and independent uniform contributions \(a_e U_e\) for the non-tree edges, with \(U_e\) uniform on \([-1/2,1/2]\). Averaging the generating functions, factor out \(\prod_e S(a_e)\). The remaining numerator is the weighted sum over arborescences oriented toward \(r\), with arc weights \(\beta\) as in the theorem, and the denominator is its value at zero. The directed matrix-tree theorem, in the row/out-degree convention, gives exactly (1); see [Chaiken](https://doi.org/10.1137/0603033) with transposition if using the column convention.

The balance is a useful direct check: \(\beta_{ij,e}-\beta_{ji,e}=-c_e a_e\). As \(u\) belongs to the flow plane, \(BCa=0\) for \(C=\operatorname{diag}(c_e)\); indeed \(a_e=\sqrt{w_e}u_e\). Thus at every vertex the total outgoing weight equals the incoming one. Both left and right null vectors of the full Laplacian are constant, and all principal cofactors agree. Reversing the reference orientation of one edge just swaps the two corresponding arc formulas.

## 3. Positive correction and exact covariance

For one edge the arithmetic mean of its two arc weights is \(\gamma_e=c_e(a_e/2)\coth(a_e/2)\), interpreted as \(c_e\) at zero. Splitting the minor into symmetric and skew terms gives
\[
A_r(u)=A_s(u)+K(u),\qquad
A_s=\sum_e\gamma_e b_e b_e^\top\succeq A.
\]
Here \(b_e\) is restricted to the remaining vertices; the diagonal terms from the skew difference vanish by \(BCa=0\) before deleting \(r\). The remaining off-diagonal skew part is the displayed \(K(u)\). Since \(x\coth x\ge1\) with equality only at zero, if \(u\ne0\) at least one \(a_e\ne0\), and in a loopless graph this raises the symmetric part by a nonzero positive semidefinite term. In particular \(\det A_s>\det A\). Also \(A_s^{-1/2}K A_s^{-1/2}\) is real skew-symmetric, with nonzero eigenvalues in pairs \(\pm i\lambda\), so
\(\det(A_s+K)=\det A_s\prod(1+\lambda^2)\ge\det A_s\). This proves strict moment-generating-function domination in (1).

Take \(u\mapsto z u\), differentiate the log of (1) twice at zero, and use
\(\log S(za)=(za)^2/24+O(z^4)\),
\(\gamma_e=c_e[1+(za_e)^2/12+O(z^4)]\),
and \(K(zu)=zK(u)\). The effective resistance is \(R_e=b_e^\top A^{-1}b_e\). The trace term from the symmetric second derivative is \(\sum_e c_e a_e^2 R_e/6\), and the negative trace of the square of the normalized skew derivative is its squared Frobenius norm. This yields (2). Strictness here also follows directly from \(R_e>0\) on every nonloop edge and some \(a_e\ne0\). Bridges have \(a_e=0\). Loops, if desired, simply split as independent interval coordinates and contribute no graph correction.

## 4. Closed second moments for complete and complete bipartite graphs

In the unweighted case use the inverse square-root of the full Laplacian on the mean-zero vertex space in (2), instead of the root-deleted coordinates. This leaves the trace and skew norm invariant: the two matrix forms are related by the invertible change of representatives modulo constants, since both full forms annihilate constants on both sides.

For \(K_N\), \(N\ge3\), each \(R_e=2/N\) and the full Laplacian is \(N I\) on the mean-zero space. The full \(K\) has squared Frobenius norm \(\frac12\sum_e a_e^2\), from its off-diagonal pair of entries for each edge. Thus the uniform flow-cell covariance is scalar with value
\[
\sigma^2(K_N)=\tfrac1{12}+\tfrac1{3N}+\tfrac1{2N^2}
\]
per unit direction. Its normalized second moment is this value divided by \(N^{2/(N-1)}\), using the tree count and cycle rank.

For \(K_{m,n}\) with \(m,n\ge2\), orient edges from the first part to the second. The flow plane is the array space with zero row and column sums, and the integral flow lattice is \(A_{m-1}\otimes A_{n-1}\). All effective resistances equal \((m+n-1)/(mn)\) since the sum over edges is the Laplacian rank. The skew form acts only between the two mean-zero part spaces (the array has zero margins), with block entries \(a_e/2,-a_e/2\) across the parts. The two Laplacian eigenvalues there are \(n\) and \(m\). Thus the weighted skew norm in (2) equals \(\sum a_e^2/(2mn)\), and
\[
\sigma^2(K_{m,n})=\tfrac1{12}+\frac{m+n+2}{6mn}.
\]
The normalized second moment is this value divided by \(m^{1/(m-1)}n^{1/(n-1)}\), from the tree count and cycle rank. For two vertices and parallel edges of arbitrary weights, the minor is one-dimensional and \(K=0\), giving the [weighted zero-sum root-family covariance](weighted-root-voronoi-covariance-optima.md).

## Comparison and scope

[Bacher–de la Harpe–Nagnibeda](https://doi.org/10.24033/bsmf.2303) relate flow lattices' Voronoi cells and determinants to circuits and spanning trees; [Dall–Pfeifle](https://arxiv.org/abs/1404.3876) give a polyhedral matrix-tree proof with weighted regular-matroid extensions. Here a root fixes the box-fiber faces and ties their centroids to the directions of tree arcs. This yields the full uniform-cell transform through a balanced directed cofactor, not just the weighted volume. The positivity statement is for the real Laplace transform and the covariance, not a coefficientwise assertion about all higher moments or about unrelated Voronoi cells. No closest-vector or cryptographic instance is used.

Replay: node verify-flow-lattice-voronoi-tree-transform.js (Node.js 18+, no dependencies). It independently compares rooted tree-mixture moments with the determinant and covariance formulas on abstract generated graphs.
