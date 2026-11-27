# The point-transitive kissing number in dimension seven is 126

**Theorem.** A finite set of unit vectors in $\mathbb R^7$ with pairwise scalar products at most $1/2$ has at most **126** points if its orthogonal symmetry group is transitive on the points. The 126 normalized roots of $E_7$ attain the bound. Together with the [six-dimensional theorem](KissingSixVertexTransitive.md), the point-transitive maxima in the two dimensions are **72 and 126**.

The geometric estimate used here holds even without a symmetry group:

> **Constant-projection theorem.** If the lengths of the orthogonal projections of all the points onto some fixed nonzero proper subspace of $\mathbb R^7$ are equal, the set has at most **126** points.

The projection length can be any constant, not just one of finitely many tested radii. Neither theorem settles the **unrestricted** seven-dimensional kissing number or classifies its extremizers. Point transitivity means one orbit of isometries of the entire set, not just a regular contact graph.

## 1. A certificate on products of two spheres

Pass to the orthogonal complement of the subspace if necessary, so its dimension $r$ is $1$, $2$ or $3$; write $s=7-r$. A point has the form $(\sqrt w\,\xi,\sqrt{1-w}\,\eta)$ for some common $w\in[0,1]$, with $\xi\in S^{r-1}$, $\eta\in S^{s-1}$. At a radius-zero endpoint one can assign arbitrary dummy directions in the vanished factor. For two distinct points put $u=\xi\cdot\xi'$, $v=\eta\cdot\eta'$. They satisfy
\[
                   wu+(1-w)v\le\tfrac12.
\]
When $r=1$, $u$ takes only the values $\pm1$.

Let $P_i^r$ be the normalized spherical Gegenbauer polynomial for ambient dimension $r$, so $P_i^r(1)=1$. In dimension two these are the Chebyshev polynomials $T_i$; in dimension one use just $P_0=1$, $P_1(u)=u$. The product kernels $P_i^r(u)P_j^s(v)$ are positive semidefinite by the addition formula in each factor and the Schur product theorem. No stronger characterization of positive kernels is needed; see [Guella–Menegatto–Peron](https://arxiv.org/abs/1503.08174) for the general product-sphere theory.

For each radius interval the [rational data](kissing-seven-product-sphere-charts.json) give a polynomial of total degree at most ten:
\[
 F(u,v)=1+\sum_{i+j>0}a_{ij}P_i^r(u)P_j^s(v),\qquad a_{ij}\ge0.
\]
It is nonpositive throughout the off-diagonal domain. Every diagonal value $F(1,1)$ is strictly below 127; the largest of the supplied rational values is $126.9700026$. For a code of size $N$, summing over ordered pairs now gives
\[
               N^2\le\sum_{x,y} F(u_{xy},v_{xy})
                      \le N F(1,1)<127N .
\]
This proves the constant-projection theorem.

| Split of ambient dimensions | $1+6$ | $2+5$ | $3+4$ |
|---|---:|---:|---:|
| Closed intervals covering all squared radii | 10 | 7 | 7 |

**How the continuum is checked.** The same polynomial applies at every $w$ in the indicated interval $[a,b]$. For fixed $(u,v)$ the scalar product is affine in $w$, so the union of permissible pairs over the interval equals the **union**, not the intersection, of the two endpoint domains. The checker verifies both.

For fixed endpoint $w<1$, the upper boundary for $v$ at $u$ is $\min(1,(1/2-wu)/(1-w))$. Split the $u$-axis where the affine expression crosses $\pm1$ and discard only intervals whose interior has empty fiber; closed endpoint fibers are included by the adjacent interval. If $r=1$, test both signs individually. If $w=1$, simply restrict $u\le1/2$. On each nonempty strip the lower boundary is $-1$ and the top is affine in $u$. Using a unit-square coordinate $t$ along the strip and $y$ in its fiber gives $u=u(t)$ and $v=-1+(1+v_{\rm top}(t))y$. A term of bidegree $(i,j)$ therefore has degree at most $i+j$ in $t$ and $j$ in $y$.

The [standard-library verifier](verify-kissing-seven-vertex-transitive.py) computes the polynomial exactly on a tensor grid of sufficient size, inverts the rational Bernstein evaluation matrices, and checks that $-F$ has nonnegative Bernstein coefficients after dyadic subdivision. This is **exact polynomial interpolation with a degree bound**, not a point-sampling test for signs. It also checks coefficient signs, the diagonal bounds, and complete coverage of $[0,1]$ separately for the three dimensions. All 24 charts pass in 1,029 Bernstein nodes. A separate check using the closed-form power coefficients of the Gegenbauer polynomials and slicing in the opposite factor passed in 1,039 nodes.

## 2. Which transitive groups could remain?

If a transitive group $G$ preserves a nonzero proper real subspace $V$, the length of projection onto $V$ is constant on each orbit. The preceding theorem therefore handles **every reducible action**. In particular a hypothetical larger transitive code must span dimension seven. Its orthogonal symmetry group acts faithfully on its points and is finite. [Tomar's unrestricted upper bound](https://www.mefyi.com/papers/kissing-numbers-five-seven/) leaves the six orders $127,\ldots,132$.

**Order 128.** A Sylow 2-subgroup $P$ is itself transitive: $|P_x|\le |G_x|_2=|P|/128$ for any point $x$, so every $P$-orbit contains at least 128 points. If $P$ acted irreducibly over $\mathbb R$ in dimension seven, its complexification would be irreducible as well. Indeed, an irreducible complex constituent and its conjugate are either equal (giving an invariant real form) or distinct with conjugation-stable direct sum; the latter would make the irreducible real dimension even. Complex irreducible degrees of a finite 2-group are powers of two, not seven. Thus $P$ preserves a proper real subspace and 128 is impossible.

For the other orders suppose $G$ is irreducible over $\mathbb R$. Its complexification is irreducible by the same odd-dimensional argument. Twist the representation by its determinant, $g\mapsto(\det g)g$, to obtain a finite subgroup $H$ of $SO(7)$ with the same invariant subspaces and the same systems of imprimitivity. The kernel has size at most two. We use $H$ to control the **odd prime factors** of $|G|$, not to assert that its modified action on the original point set is transitive.

**Imprimitive action.** An imprimitive irreducible complex representation of prime degree seven permutes seven complex lines transitively. The kernel $B$ of this permutation action is diagonal in those lines and abelian. If all its weights agree, it consists of real scalar orthogonal matrices, so has order at most two. Otherwise the characters of $B$ on the seven lines are all distinct: equal-weight classes have the same size by transitivity, and seven is prime. Complex conjugation permutes these seven weight lines and fixes at least one, since seven is odd. It commutes with the real group action, so it fixes each of the seven lines individually. The diagonal characters of $B$ are consequently real and take values in $\{\pm1\}$. In either case $|B|$ is a power of two and the quotient embeds in $S_7$. No prime exceeding seven divides $|H|$.

**Primitive action.** Apply [Wales, *Finite Linear Groups of Degree Seven II*, Theorem I](https://msp.org/pjm/1970/34-1/pjm-v34-n1-p21-p.pdf). Its hypotheses are worth noting. The complex representation of $H$ is faithful, irreducible, primitive and of determinant one. Its Sylow 7-subgroup is abelian: the nontrivial irreducible characters of an odd order group are not self-conjugate (squaring permutes the group, so their Frobenius–Schur indicator is zero). A nonlinear complex constituent of a 7-group has degree at least seven and would require its distinct conjugate in the real representation, impossible in real dimension seven. Thus the restriction splits into linear complex characters and the faithfully represented subgroup commutes.

The only consequence of Wales's list needed here is that **if a prime larger than seven divides $|H|$, it is 13, and the same order is not divisible by 5**. Indeed the exceptional factor is $\mathrm{PSL}_2(13)$ of order $1092=2^2\cdot3\cdot7\cdot13$; all other listed factors and their indicated extensions have no prime divisor above seven, and the possible central factor has order one or seven. The determinant twist changes no odd prime divisors.

Finally $N$ divides $|G|$ by orbit–stabilizer. The orders $127$, $129=3\cdot43$, $131$ and $132=12\cdot11$ need a prime excluded in both irreducible cases. The remaining order $130=2\cdot5\cdot13$ requires 5 and 13 together, also impossible. This proves the upper bound of 126. The normalized roots of the simply laced irreducible system $E_7$ form one Weyl-group orbit and give the matching lower bound.

**Replay:** `python3 verify-kissing-seven-vertex-transitive.py`, with [the JSON data](kissing-seven-product-sphere-charts.json) in the same directory. The chart searches used numerical linear programming; the result depends only on the enclosed rational data, exact checks and the cited theorems.