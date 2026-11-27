# The minimum non-antipodal design of a single odd harmonic index

Let $k$ be a positive odd integer, and let $X$ be a finite set of distinct points on the unit sphere in **real ambient dimension $d\ge4$**. Suppose
$$
                 \sum_{x\in X} H(x)=0
$$
for every real homogeneous harmonic polynomial $H$ of degree **exactly $k$**. There is no assumption on lower degrees.

**Theorem.** Remove all antipodal pairs from $X$. Either nothing remains or at least $k+2$ points remain. If exactly $k+2$ remain, they are the vertices of a regular $(k+2)$-gon on a great circle. Conversely such a polygon, with any disjoint collection of antipodal pairs, has harmonic index $k$. Thus the minimum non-antipodal cardinality is exactly $k+2$, and the minimum is unique up to isometry.

[Misawa, Munemasa and Sawa](https://arxiv.org/html/2410.09471v6) obtained the minimum $k+2$ under the **simultaneous** conditions at $1,3,\ldots,k$, in every ambient dimension $d\ge2$. Their regular-polygon construction is also the example here. Our result needs just one index when $d\ge4$, and classifies equality. It implies uniqueness of the minimum under their simultaneous conditions also for $d=2,3$, by embedding into $\mathbb R^4$: the restriction of a homogeneous degree-$k$ polynomial decomposes on the smaller sphere into harmonics of degrees $k,k-2,\ldots,1$. This does not determine all sizes or prescribe the set of *all* harmonic indices of a design. [Misawa and Nishimura, Theorem 2.7](https://arxiv.org/html/2607.01761v1) give bounds for large indices using a code's inner products. For fixed-degree interpolation more generally, see [Ron and Sun](https://doi.org/10.1090/S0025-5718-96-00780-6).

The ambient dimension restriction for the **single-index** result matters. In $\mathbb R^3$ the four vertices of a regular tetrahedron have harmonic index $5$: the normalized Legendre polynomial satisfies $P_5(-1/3)=-1/3$, so the sum of its kernel over the four diagonal and twelve off-diagonal pairs vanishes, which by the addition formula is equivalent to harmonic balance. Four is less than seven.

## 1. A family of harmonic tests in four real coordinates

All calculations may be complexified. Antipodal pairs cancel because $k$ is odd. The remaining points represent distinct real projective directions. If $d>4$, orthogonally project them onto a generic four-space. Require that every independent subset of at most three of these vectors retains its rank. For each such subset this holds on a dense open set: the Gram determinant of its projection is a real-analytic function on the connected Grassmannian, nonzero when the four-space contains its span. There are finitely many subsets. The projected vectors need not be unit, but any harmonic polynomial on the four-space pulls back by orthogonal projection to a harmonic polynomial on the original space. Thus they satisfy the same homogeneous relations, and any noncoplanar triple would remain noncoplanar.

Identify a vector $y$ in the four-space with $(z,w)\in\mathbb C^2$ and write
$$
 Q(y)=\begin{pmatrix} z&w\\-\bar w&\bar z\end{pmatrix}.
$$
This real-linear identification is closed under matrix multiplication and inversion of nonzero elements; $Q^*Q=\|y\|^2I$. For each $v=(a,b)^t\ne0$, the map $y\mapsto Q(y)v$ is a real-linear similarity onto $\mathbb C^2$. Its component forms are $az+bw$ and $-a\bar w+b\bar z$. Any homogeneous binary polynomial $p$ of degree $k$ in these two forms is harmonic in $y$: each form's gradient has bilinear square zero and their mixed gradient product is proportional to $ab-ba=0$. Apply the chain rule for the Laplacian. In particular, if $y_i$ are the projected residual points, harmonic balance implies
$$
                      \sum_i p(Q(y_i)v)=0 \tag{1}
$$
for every $v$ and every such $p$.

Put $D_{ij}(v)=\det(Q(y_i)v,Q(y_j)v)$. Its zero lines in $\mathbb C^2$ are the eigenlines of $Q(y_i)^{-1}Q(y_j)$. This is a nonscalar quaternion matrix, since the real directions are distinct and the only scalar quaternion matrices are real scalars. It is a scalar multiple of a unitary matrix and has two distinct eigenvalues. In an eigenbasis $D_{ij}$ is a nonzero multiple of $v_1v_2$. In particular its two projective zeros are simple. Generic $v$ avoids all these zeros, so the images are projectively distinct binary vectors.

With $r\le k+1$ nonzero such images a degree-$k$ binary polynomial can vanish on any $r-1$ of their lines without vanishing on the last: multiply one linear form per unwanted line, then pad by a nonvanishing linear form to degree $k$. This contradicts (1). The lower bound follows, even for a relation with arbitrary nonzero scalar weights.

## 2. Rigidity at the first dependence

Suppose $r=k+2$. Write $Q(y_i)v=(a_i,b_i)$ and $t_i=b_i/a_i$ for generic $v$. The relations in (1), on the $k+1$ monomials, are
$$
                    \sum_i a_i^k t_i^j=0,\qquad 0\le j\le k.
$$
The Vandermonde nullspace is one-dimensional and is spanned by the entries $1/\prod_{h\ne i}(t_i-t_h)$ (compare the leading coefficient in Lagrange interpolation at $r$ nodes). Thus $a_i^k\prod_{h\ne i}(t_i-t_h)$ is independent of $i$. Clearing the common denominator $\prod_h a_h$, using $k=r-2$, gives the identities
$$
               \prod_{h\ne i}D_{ih}(v)=\prod_{h\ne j}D_{jh}(v) \quad\text{for all }i,j. \tag{2}
$$
They hold as binary polynomial identities by density. With nonzero weights the two products would differ only by nonzero constant factors; the next step is the same.

For **any** $v\ne0$, partition the points by the complex projective lines $[Q(y_i)v]$. The order of vanishing of the product in (2) at $[v]$ is exactly the size of the class of $i$ minus one, by simplicity of every individual zero. Therefore every class has the same size, a divisor of the odd integer $r$. Given any two indices, choose an eigenline of $Q(y_i)^{-1}Q(y_j)$ to put them in the same class. This class has odd size at least three. Its points lie in a common real two-plane: they are the inverse image of a complex line under the real-linear isomorphism $y\mapsto Q(y)v$. We have shown that every projective line through two directions contains a third.

The real Sylvester–Gallai theorem now puts all projective directions on a single line, i.e. all vectors in a real two-plane. Here is the elementary ordinary-line argument if needed. Choose an affine chart meeting all the points and generically project to a plane preserving the distinctions of points and noncollinear triples. If they are noncollinear, choose a point $A$ and a line through two points at minimum **positive** distance $h$ from $A$. If that line has at least three points, two, $B,C$, lie on the same closed side of the perpendicular foot, with $B$ closer to the foot. Then the distance from $B$ to the line $AC$ is $h|BC|/|AC|<h$, a contradiction. The projected four-space preserved every originally noncoplanar triple, so the original unit vectors also lie in a two-plane.

## 3. The only planar equality case

On the two-plane identify unit points with $z_i=e^{i\theta_i}$. The restriction of the ambient harmonic tests includes every homogeneous polynomial of degree $k$ on that plane. For example, in orthonormal coordinates with the plane first, every polynomial in $x_1+i x_3$ and $x_2+i x_4$ is harmonic; replacing the two variables of a given binary polynomial by these forms extends it. Taking the polynomials restricting to $z^\ell|z|^{k-\ell}$ gives
$\sum_i z_i^\ell=0$ for every odd $1\le\ell\le k$. Newton's identities give $e_j=0$ for all odd $j\le k$, where $e_j$ are the elementary symmetric functions of the $r=k+2$ unit roots. For $1\le j<r$, the identity $e_{r-j}=e_r\overline{e_j}$ covers the even indices too. Hence the monic polynomial with the $z_i$ as roots is $z^r-C$ with $|C|=1$. This is the regular polygon. Conversely any homogeneous polynomial of odd degree $k$ on this circle has only nonzero Fourier frequencies of magnitude at most $k$, none divisible by $k+2$; it sums to zero on the polygon.

For a separation-sensitive enhancement and an application to arbitrary six- and seven-dimensional kissing codes, see [Single-harmonic obstructions](KissingSingleHarmonicObstructions.md).
