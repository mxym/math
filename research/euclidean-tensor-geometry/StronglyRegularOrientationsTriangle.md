# Directed triangles in orientations of strongly regular graphs

**Yongxian Zhang.** AI-assisted proof development and internal verification.

**Theorem.** Let \(D\) be an orientation of a strongly regular undirected graph on \(n\) vertices. If \(\delta^+(D)\ge 5n/16\), then \(D\) contains a directed triangle. No minimum indegree assumption is needed. This is an upper threshold for this class, not a claim of sharpness: balanced blow-ups of a directed four-cycle give lower threshold \(n/4\) in this class. The general Caccetta–Häggkvist triangle conjecture is unaffected.

Write \(d=\lceil5n/16\rceil\), let \((n,k,\lambda,\mu)\) be the strongly regular parameters, and suppose there is no directed triangle. The adjacency matrices of \(D\) and its underlying graph are \(A\) and \(S=A+A^{\mathsf T}\). Put \(K=A-A^{\mathsf T}\), \(H=-K^2=K K^{\mathsf T}\), \(x=k/n\). Then \(k\ge2d\) by averaging the outdegrees, and \(k\ge5n/8\); in particular the underlying regular graph is connected, since two components would need at least \(2(k+1)>n\) vertices.

Choose a vertex \(v\) of outdegree at most \(k/2\). Its nonempty outneighborhood is triangle-free. By the [Hladký–Král’–Norin triangle bound](https://arxiv.org/abs/0908.2791), it has a vertex \(w\) of internal outdegree less than \((7/20)|N^+(v)|\), since \(0.3465<7/20\). No outarc from \(w\) reaches \(v\) or any inneighbor of \(v\): these would give a digon or a directed triangle. Consequently with \(\ell=n-k-1\),
\[
40(d-\ell)\le7k,\qquad 5/8\le x<5/6.
\]
The latter follows from \(k\ge2d\) and \((33/40)k\le n-1-d\). A complete graph is excluded directly by \(d\le7k/40\) if \(\ell=0\).

## Spectral estimate

Let \(r\) be the largest nonprincipal eigenvalue of \(S\) and \(P=\boldsymbol 1\boldsymbol 1^{\mathsf T}/n\). For a connected regular graph \(S\preceq rI+(k-r)P\). Since \(H\succeq0\),
\[
 \operatorname{tr}(SH)\le r n k+(k-r)\|K\boldsymbol 1\|^2/n ,
\]
where \(\operatorname{tr}(H)=nk\) follows because \(K\) has a unit-magnitude entry on every oriented adjacency in either order and zero otherwise. The values \(z_v=(K\boldsymbol 1)_v=2d^+(v)-k\) have mean zero and lie in \([-a,k]\) for \(a=k-2d\). Averaging \((z_v+a)(k-z_v)\ge0\) gives \(\|K\boldsymbol 1\|^2/n\le ak\). Finally \(\operatorname{tr}(S^3)=nk\lambda\) by strong regularity, and cyclicity of the trace and skew symmetry give
\[
0=\operatorname{tr}(A^3)
=\tfrac18\bigl(\operatorname{tr}(S^3)-3\operatorname{tr}(SH)\bigr).
\]
That is, \(\lambda\le3r+3(k-r)a/n\). For any edge the two neighborhoods have union of size at most \(n\), so \(\lambda\ge2k-n\). Using \(a/n\le x-5/8\) leads to
\[
3(1-x+5/8)\frac rn\ \ge\ 2x-1-3x(x-5/8).
\]
Subtract \((9/50)(1-x+5/8)\) from the right side. The result is concave on \([5/8,5/6]\) with values \(7/100\) and \(1/300\) at the endpoints, respectively. Thus \(r\ge3n/50>0\).

## Bounding the order and replay

Since the graph is connected and not complete, \(1\le\mu\le k\); when \(\mu=k\), nonadjacent vertices have identical neighborhoods, hence the graph is complete multipartite and \(r=0\), impossible. Indeed in a regular complete multipartite graph, on the space orthogonal to \(\boldsymbol 1\) the adjacency quadratic form is minus the sum of the squared coordinate sums on the parts. Thus \(1\le\mu<k\).

The matrix identity \(S^2=(k-\mu)I+(\lambda-\mu)S+\mu J\) shows the nonprincipal eigenvalues are \(r,s\) with \(r>0>s\) and discriminant \(\Delta=(\lambda-\mu)^2+4(k-\mu)\). Both occur, since otherwise \(S\) would be a linear combination of \(I,J\), impossible for the connected noncomplete graph. If \(\Delta\) were nonsquare, the irrational contributions to \(\operatorname{tr} S=0\) would force the multiplicities equal, so \(2k/(n-1)=\mu-\lambda\), an integer strictly between 1 and 2, impossible. Hence \(r,s\) are integers. Write \(f\) for the multiplicity of \(r\); then
\[
 fr^2\le\operatorname{tr}(S^2)-k^2=k(n-k)\le 15n^2/64,
 \qquad f\le65.
\]
There is also the usual absolute bound \(n\le f(f+3)/2\). For completeness the rank-\(f\) spectral projector is \(E=(S-sI-(k-s)P)/(r-s)\). Its diagonal is constant positive, and its off-diagonal entries take one value on edges and one on nonedges. Normalize its column vectors to unit vectors (their Gram matrix is \(E\) divided by its diagonal). The two off-diagonal inner products are \(r/k\) and \(-(r+1)/(n-k-1)\), obtained from \(SE=rE\) and \(E\boldsymbol 1=0\), and neither equals 1. On the unit sphere in \(\mathbb R^f\), the \(n\) quadratic functions formed by taking the product of the two linear factors for each vector vanish on every other vector but not on their own. They are linearly independent, and polynomial functions of degree at most two on the sphere have dimension at most \(\binom{f+2}{2}-1=f(f+3)/2\), by the sphere equation. Therefore \(n\le2210\).

Enumerate \(3\le n\le2210\), \(2d\le k<n-1\), \(1\le\mu<k\) and apply
\[
 k(k-1-\lambda)=(n-k-1)\mu,\quad
 f=\frac{-k-(n-1)s}{r-s},\quad
 nk\lambda\le3rnk+3(k-r)ak.
\]
The first condition counts edges from the neighborhood of a fixed vertex to its nonneighbors. Require integer \(\lambda,r,s,f\), both eigenvalue multiplicities positive, the absolute bound, and the local degree inequality above. The companion script verifies that the unique survivor is \((n,k,\lambda,\mu)=(16,10,6,6)\) with \((r,s,f)=(2,-2,5)\). No graph is enumerated.

## The remaining graph

Here \(\delta^+\ge5=k/2\) implies all vertices have outdegree 5, so \(K\boldsymbol 1=0\). Equality \(\lambda=3r=6\) in the trace inequality implies that the range of the PSD matrix \(H\), hence the range of \(K\), lies in the \(r\)-eigenspace. Equivalently if \(E\) projects onto that eigenspace, \(K=EKE\): equality in \(\operatorname{tr}((rI+(k-r)P-S)H)\ge0\) forces zero range in the \(s\)-space, and \(K\boldsymbol 1=0\) excludes the principal space.

The graph with parameters \((16,10,6,6)\) is the complement of the unique \((16,5,0,2)\)-graph (Godsil–Royle, *Algebraic Graph Theory*, Theorem 10.6.4; see also [Brouwer's graph page](https://aeb.win.tue.nl/graphs/Clebsch.html)). Use the model on sign vectors \(x\in\{\pm1\}^5\) of product 1, adjacent when they differ in exactly two signs; its complement is the folded five-cube (nonidentity flips of four coordinates). The five coordinate functions are orthogonal and each has eigenvalue \(\binom42-4=2\), so they span the \(r\)-eigenspace. Thus \(K_{xy}=x^{\mathsf T}B y\) for a real skew-symmetric \(5\times5\) matrix \(B\). For any \(i\), let \(y\) agree with \(x\) on \(i\) and differ elsewhere: \(x,y\) are nonadjacent. Then
\[
0=K_{xy}=2 x_i\sum_{j=1}^5 B_{ji}x_j,
\]
because \(y=-x+2x_i e_i\). Orthogonality of the coordinate functions forces the entire \(i\)-th column of \(B\) to vanish. Hence \(K=0\), incompatible with orienting any edge. This eliminates the last case.

The proof combines a cubic trace, a positive-semidefinite Gram constraint, a two-distance embedding, and a small integer check. The lower bound is realized on \(K_{2m,2m}\) by dividing each part into two size-\(m\) groups and directing all edges between successive groups on a four-cycle. Thus the best threshold in this class lies between \(1/4\) and \(5/16\); no equality characterization at an optimal threshold is claimed.
