# Directed triangles in orientations of strongly regular graphs

**Yongxian Zhang.** AI-assisted proof development and internal verification.

**Theorem.** Every orientation of a strongly regular graph on \(n\) vertices with minimum outdegree at least \(7n/25\) contains a directed triangle. There is no minimum indegree condition. This strengthens the earlier \(5n/16\) bound for this class. Balanced orientations of \(K_{2m,2m}\) around a four-cycle show that the optimum cannot be below \(1/4\); we do not assert sharpness or an unrestricted Caccetta–Häggkvist bound.

Write \(d=\lceil7n/25\rceil\) and let \(k,\lambda,\mu\) be the underlying strongly regular graph parameters. Suppose the digraph contains no directed triangle. Write \(\ell=n-k-1\). For every vertex \(v\), its nonempty outneighborhood has some vertex \(w\) with internal outdegree less than \(c d_v^+\), where \(c=693/2000\), by [Hladký–Král’–Norin](https://arxiv.org/abs/0908.2791). No outarc from \(w\) can go to \(v\) or an inneighbor of \(v\). Thus \(d< c d_v^++\ell\) and the actual minimum outdegree is at least
\[
 d_1=\max\!\left(d,1+\left\lfloor 2000(d-\ell)/693\right\rfloor\right).
\]
In particular \(k\ge2d_1\ge14n/25\) by averaging. The host is connected by its degree, and is not complete: if \(\ell=0\), averaging \(d<c d_v^+\) gives \(d<ck/2<7n/25\).

## Local spectral trace

Write \(A\) for the directed adjacency, \(S=A+A^{\mathsf T}\), \(K=A-A^{\mathsf T}\), \(z_v=2d_v^+-k\), \(a=k-2d_1\), and \(r\) for the largest nonprincipal eigenvalue of \(S\). The column \(y_v\) of \(K\) is supported on the \(k\) neighbors of \(v\), has squared norm \(k\), and has sum \(-z_v\). Each neighborhood graph is \(\lambda\)-regular, and its Rayleigh quotient on mean-zero vectors is at most \(r\), by extension by zero in the host. Decomposing \(y_v\) into its local mean and mean-zero part gives
\[
y_v^{\mathsf T} S y_v\le rk+(\lambda-r)z_v^2/k .
\]
On the other hand, cyclicity and skew symmetry in the expansion of \(\operatorname{tr}(S+K)^3\) give
\[
0=8\operatorname{tr}(A^3)=nk\lambda-3\operatorname{tr}(S K K^{\mathsf T}).
\]
Consequently with \(V=n^{-1}\sum_v z_v^2\),
\[
\lambda\le3r+3(\lambda-r)V/k^2. \tag{1}
\]
The \(z_v\) have mean zero and lie in \([-a,k]\). Averaging \((z_v+a)(k-z_v)\ge0\) gives \(V\le ak\). Consequently \(k(\lambda-3r)\le3(\lambda-r)a\) when \(\lambda\ge r\); if \(\lambda<r\) that last inequality also holds, since \(a\le k\) and \(\lambda\ge0\).

## Cutting the order down to a finite calculation

Put \(x=k/n\), \(B=a/n\), \(R=17/1000\). From the degree bounds
\[
0\le B\le C(x)=\min\!\left(x-\frac{14}{25},
 x-2(7/25+x-1)/c\right).
\]
The switch point is \(x_0=40851/50000\). Since \(\lambda\ge2k-n\), if \(r<Rn\) then \(\lambda>r\) and the previous inequality gives
\[
(2x-1)(x-3B)\le 3(r/n)(x-B)<3R(x-B).
\]
Here \(x-3B>0\) because \(x-3C(x)>0\): on the left it is \(42/25-2x\), and on the right it is increasing from the positive value at \(x_0\). Also \(x-B>0\). For \(F(x)=(2x-1)(x-3C(x))-3R(x-C(x))\), the preceding strict inequality would give \(F(x)<0\), because the same expression decreases as \(B\) increases to \(C(x)\) (as \(2x-1>R\)). But \(F\) is concave on \([14/25,x_0]\), with endpoint values \(483/12500\) and \(362799/625000000\). For \(x\ge x_0\) the slope \(m=1-2/c\) of \(C\) lies in \((-5,-4)\); the derivative of \(F\) is \(2(x-3C)+(2x-1)(1-3m)-3R(1-m)>0\). This proves \(r\ge17n/1000\).

Since the graph is connected and not complete, \(1\le\mu\le k\); when \(\mu=k\), nonadjacent vertices have identical neighborhoods, hence the graph is complete multipartite and \(r=0\), impossible. Indeed in a regular complete multipartite graph, on the space orthogonal to \(\boldsymbol 1\) the adjacency quadratic form is minus the sum of the squared coordinate sums on the parts. Thus \(1\le\mu<k\).

The matrix identity \(S^2=(k-\mu)I+(\lambda-\mu)S+\mu J\) shows the nonprincipal eigenvalues are \(r,s\) with \(r>0>s\) and discriminant \(\Delta=(\lambda-\mu)^2+4(k-\mu)\). Both occur, since otherwise \(S\) would be a linear combination of \(I,J\), impossible for the connected noncomplete graph. If \(\Delta\) were nonsquare, the irrational contributions to \(\operatorname{tr} S=0\) would force the multiplicities equal, so \(2k/(n-1)=\mu-\lambda\), an integer strictly between 1 and 2, impossible. Hence \(r,s\) are integers. Write \(f\) for the multiplicity of \(r\); then
\[
 fr^2\le\operatorname{tr}(S^2)-k^2=k(n-k)\le n^2/4,
 \qquad f\le865.
\]
There is also the usual absolute bound \(n\le f(f+3)/2\). For completeness the rank-\(f\) spectral projector is \(E=(S-sI-(k-s)P)/(r-s)\). Its diagonal is constant positive, and its off-diagonal entries take one value on edges and one on nonedges. Normalize its column vectors to unit vectors (their Gram matrix is \(E\) divided by its diagonal). The two off-diagonal inner products are \(r/k\) and \(-(r+1)/(n-k-1)\), obtained from \(SE=rE\) and \(E\boldsymbol 1=0\), and neither equals 1. On the unit sphere in \(\mathbb R^f\), the \(n\) quadratic functions formed by taking the product of the two linear factors for each vector vanish on every other vector but not on their own. They are linearly independent, and polynomial functions of degree at most two on the sphere have dimension at most \(\binom{f+2}{2}-1=f(f+3)/2\), by the sphere equation. Therefore \(n\le375410\).

## Sharper imbalance bound and exact parameter replay

Order the nonnegative excesses \(w_v=d_v^+-d_1\) in decreasing order. The first \(i\) have sum at most
\[
U_i=\min\!\left(na/2,\ (k-d_1)i,\ (k-d_1-s/2)i-\frac{k-s}{2n}i^2\right).
\]
The first two bounds are total and pointwise limits. For a set of \(i\) vertices the host's minimum eigenvalue \(s\) bounds its internal edges below by \((s i+(k-s)i^2/n)/2\), via its indicator and the principal projector. These edges contribute to that set's indegree sum. Subtract this bound from the \(i(k-d_1)\) available degree excess to get the third bound. The minimum of these three concave functions is concave, \(U_0=0\) and \(U_n=na/2\). Hence \(U_i-U_{i-1}\) is a decreasing sequence that majorizes the excesses. Summation by parts applied to the difference of the two square sums (factor each difference of squares) gives
\[
 V \le \frac4n\sum_{i=1}^n(U_i-U_{i-1})^2-a^2. \tag{2}
\]

In the exact enumeration use \(t=-s\ge2\) and \(rt=k-\mu\); as \(rt<n\) and \(r\ge17n/1000\), \(t\le58\). The standard parameter identity \(k(k-1-\lambda)=\ell\mu\), with \(\lambda=\mu+r-t\), becomes
\[
 \ell\mu=k(r+1)(t-1).
\]
In particular \(t=1\) is impossible, and \(\mu\) divides \(rt(r+1)(t-1)\). For each \(r,t\), the replay enumerates these positive divisors and sets \(k=rt+\mu,\ \ell=(r+1)(t-1)\big(1+rt/\mu\big)\) and \(n=k+\ell+1\). Its other filters are the required outdegree, the positive integral multiplicities \(f=(-k-(n-1)s)/(r-s)\) and \(n-1-f\), the derived \(r,f,n\) bounds, the complement parameter \(n-2-2k+\mu\ge0\), and the first Krein bound \((r+1)(k+r+2rs)\le(k+r)(s+1)^2\), as in [Brouwer–Haemers, *Spectra of Graphs*, Chapter 9](https://aeb.win.tue.nl/2WF02/spectra.pdf) (Krein conditions). Finally it applies (1) first with \(V\le ak\) and then with (2) when \(\lambda\ge r\). To implement (2) exactly let \(T_i=2nU_i\), an integer. Its right side is \(\big(\sum_i(T_i-T_{i-1})^2-a^2n^3\big)/n^3\).

The [companion Node.js replay](verify_strongly_regular_orientations.js) leaves 23 tuples before the sharper imbalance estimate and only the following after it:
\[
(n,k,\lambda,\mu;r,s,f)=
(10,6,3,4;1,-2,4),\quad (16,10,6,6;2,-2,5),\quad (27,16,10,8;4,-2,6).
\]
It uses integer parameter arithmetic and BigInt for (2). All three cases have \(d=k/2\), so the orientation is balanced and every \(y_v\) has mean zero.

## Eliminating the three cases

**Order 10.** The complement is the unique Petersen graph, so the host is the triangular graph on two-subsets of a five-element set, adjacent when intersecting ([Brouwer–Van Maldeghem, §10.3](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf)). The neighborhood of \(\{i,j\}\) consists of two triples (sharing \(i\) and sharing \(j\)), each a clique, joined by the matching of equal third element. Its nonprincipal largest eigenvalue is \(1\), simple, with eigenvectors constant and of opposite signs on the two triples; this follows directly from the block matrices \(J_3-I_3\) on the diagonal and \(I_3\) off the diagonal. Since \(\lambda=3\), the trace condition forces equality in every local Rayleigh estimate, so \(y_v\) is constant on each triple. In the four-clique of all pairs containing a fixed \(i\), this would make every vertex a source or a sink within the clique, impossible in a tournament on four vertices.

**Order 16.** Here \(\delta^+\ge5=k/2\) implies all vertices have outdegree 5, so \(K\boldsymbol 1=0\). Put \(H=KK^{\mathsf T}\) and \(P=\boldsymbol1\boldsymbol1^{\mathsf T}/n\). The trace identity gives \(\operatorname{tr}(SH)=nk\lambda/3=r\operatorname{tr}H\). As \(S\preceq rI+(k-r)P\) and \(K\boldsymbol1=0\), equality implies that the range of \(H\), hence the range of \(K\), lies in the \(r\)-eigenspace. Equivalently if \(E\) projects onto that eigenspace, \(K=EKE\): equality in \(\operatorname{tr}((rI+(k-r)P-S)H)\ge0\) forces zero range in the \(s\)-space, and \(K\boldsymbol 1=0\) excludes the principal space.

The graph with parameters \((16,10,6,6)\) is the complement of the unique \((16,5,0,2)\)-graph (Godsil–Royle, *Algebraic Graph Theory*, Theorem 10.6.4; see also [Brouwer's graph page](https://aeb.win.tue.nl/graphs/Clebsch.html)). Use the model on sign vectors \(x\in\{\pm1\}^5\) of product 1, adjacent when they differ in exactly two signs; its complement is the folded five-cube (nonidentity flips of four coordinates). The five coordinate functions are orthogonal and each has eigenvalue \(\binom42-4=2\), so they span the \(r\)-eigenspace. Thus \(K_{xy}=x^{\mathsf T}B y\) for a real skew-symmetric \(5\times5\) matrix \(B\). For any \(i\), let \(y\) agree with \(x\) on \(i\) and differ elsewhere: \(x,y\) are nonadjacent. Then
\[
0=K_{xy}=2 x_i\sum_{j=1}^5 B_{ji}x_j,
\]
because \(y=-x+2x_i e_i\). Orthogonality of the coordinate functions forces the entire \(i\)-th column of \(B\) to vanish. Hence \(K=0\), incompatible with orienting any edge. This eliminates order 16.

**Order 27.** The local graph of the Schläfli graph is the halved five-cube just used, of parameters \((16,10,6,6)\). One can see this directly, without uniqueness of the 27-vertex host. In the complement with parameters \((27,10,1,5)\), every edge lies in exactly one triangle, called a line. There are 45 lines, five through a fixed vertex \(v\). An outside vertex has at most one neighbor on any line; the ten neighbors of \(v\) account for all 40 lines not through \(v\) (four per neighbor). Thus every non-\(v\) line has one neighbor of \(v\). The neighborhood of \(v\) in the complement is five disjoint pairs. Each of its sixteen nonneighbors has exactly five neighbors in it and uses exactly one per pair (two from a pair would give the pair two common neighbors). Label these choices with five bits. Any two adjacent nonneighbors agree in exactly one bit, because their line has exactly one \(v\)-neighbor and adjacent vertices have only one common neighbor. For a fixed nonneighbor, the five possible agreeing coordinates occur once each among its five neighbors inside the nonneighbor set: repetitions would give two common neighbors to its edge with the corresponding shared \(v\)-neighbor. The set of observed labels is therefore closed under the five weight-four flips, which generate the even binary subspace on five bits. With sixteen vertices this is exactly one translated even cube, with edges the weight-four flips. Complementing yields the asserted local halved cube. Its nonprincipal top eigenvalue is \(2\), so the local trace estimate with this value would give \(\lambda\le6\), contrary to \(\lambda=10\).

Finally the lower-bound example is the orientation of \(K_{2m,2m}\) obtained by splitting each part in half and directing edges cyclically among the resulting four groups. Its minimum outdegree is \(m=n/4\) and it has no directed triangle. The interval between this example and \(7/25\) is not settled here.
