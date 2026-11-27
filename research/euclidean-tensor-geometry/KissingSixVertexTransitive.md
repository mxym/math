# The point-transitive kissing number in dimension six is 72

**Theorem.** A set of unit vectors in $\mathbb R^6$ with pairwise inner products at most $1/2$, whose orthogonal symmetry group acts transitively on its points, contains at most **72** points. The normalized $E_6$ roots attain 72: the Weyl group is transitive on the roots of this irreducible simply laced system.

Transitivity means that an isometry preserving the **point set** can carry any chosen point to any other. It does not mean merely that all points have the same number of contacts. No integrality, antipodality, or prescribed root subsystem is assumed. **The unrestricted six-dimensional kissing number remains open.** This result does not classify the transitive 72-point maximizers.

[Tomar's unrestricted bound](https://www.mefyi.com/papers/kissing-numbers-five-seven/) leaves precisely four orders to exclude. The following table summarizes the proof.

| Order | Obstruction |
|---:|---|
| 73 | A 73-cycle cannot be a six-dimensional kissing orbit. |
| 74 | Two compatible 37-point orbits of a common rotation do not exist. |
| 75 | A Sylow 5-subgroup must give three free 25-point orbits. Neither $C_{25}$ nor $C_5^2$ can do this. |
| 76 | A normal 19-subgroup forces the transitive set onto one flat three-torus, which admits at most 70 kissing points. |

The argument also yields a restriction **without** transitivity. In dimension six, the prime divisors of the symmetry-group order of any 73-, 74- or 75-point kissing set belong to $\{2,3,5,7\}$. For 76 points only 19 can be added. In seven dimensions all 127–132-point kissing sets have symmetry-group prime divisors in $\{2,3,5,7,11,13\}$. In particular 127, 129 and 131 cannot be transitive orders in dimension seven; nothing here excludes all remaining excess orders in that dimension.

## 1. Odd rotations and their fixed points

All the excess sets under discussion span the ambient space by the known lower-dimensional upper bounds, so their orthogonal symmetry groups are finite and act faithfully on their points. Let a nonidentity symmetry have odd prime order $p$. On its nonfixed subspace it is a direct sum of real rotation planes with frequencies $k$ modulo $p$, identified up to sign. On a nonfixed orbit remove the common fixed-vector component and normalize: this can only decrease pairwise inner products, since $(t-h)/(1-h)\le t$ for $h\in[0,1)$, $t\le1$. On repeated isotypic planes the contributions add. Thus, with the distinct active frequencies $k_i$, the squared radii $w_i$ must satisfy
\[
 w_i\ge0,\qquad\sum_iw_i=1,\qquad
 \sum_i w_i\cos(2\pi jk_i/p)\le\tfrac12\quad(1\le j<p).
 \tag{1}
\]
Conversely these are ordinary conditions for **one** cyclic orbit; they are not a test for two separate orbits.

In dimensions at most seven there are at most three active frequencies. The [exact checker](verify-kissing-six-vertex-transitive.py) exhausts all frequency sets in (1), allowing zero weights. Up to sign, order and multiplication by a unit, normalize one frequency to 1. Exact rational outer polygons yield the following necessary numbers of active rotation planes (only primes up to 132 are needed because the group acts faithfully on at most 132 points).

| Prime | $7,11,13$ | $17$ through $41$ | $43$ through $131$ |
|---|---:|---:|---:|
| Minimum number of planes | 2 | 3 | at least 4 (impossible here) |

If at least $r$ planes are needed, the fixed points lie in dimension at most $n-2r$. Their count is congruent to $N$ modulo $p$. The kissing maxima in dimensions $0,1,2,3$ are $0,2,6,12$. This proves the prime-divisor restrictions stated above, except for 37 at 74 points, handled in §3. By orbit–stabilizer any transitive order $N$ divides the group order. This already disposes of 73, and of the three stated odd orders in dimension seven.

## 2. Why 75 points force three abelian orbits of order 25

Let $G$ be transitive on 75 points and let $P$ be a Sylow 5-subgroup. For any point $x$, $|P_x|\le |G_x|_5=|G|_5/25$, where $|H|_5$ is the largest power of 5 dividing $|H|$. Every $P$-orbit therefore has size at least 25; the next power of 5 after 25 is 125. All three orbits have size exactly 25.

The group $P$ is abelian in its faithful real representation of degree six. Indeed complex irreducible degrees of a 5-group are powers of five. Every nontrivial irreducible character has Frobenius–Schur indicator zero: squaring permutes this odd order group, and the sum of the character over the group is zero. A non-linear constituent of a real representation would therefore require two distinct conjugate constituents of dimension at least five each. All constituents here are linear, so their faithful image commutes.

Nontrivial characters of $P$ come in conjugate pairs, each a real rotation type. An individual orbit cannot have just one or two active types: after removing the fixed projection, its Gram matrix has rank at most four, with scalar products still at most $1/2$, but [the four-dimensional kissing number is 24](https://annals.math.princeton.edu/2008/168-1/p01). Hence the representation consists exactly of three distinct real rotation planes, and every orbit representative has nonzero projection on all three. If an element fixes one representative, all three characters take the value 1 on that element, so it is the identity on the ambient space. Thus $P$ acts freely and $|P|=25$. This deduction does not assume $P$ is normal in $G$.

For $P=C_{25}$, a faithful frequency triple contains a unit; normalize it to 1 as in (1). For $P=C_5^2$, the three coordinates of the rotation angles form a two-dimensional linear subspace in $\mathbb F_5^3$, the kernel of one nonzero row $H$. Permuting/sign-changing columns and multiplying $H$ by a nonzero scalar do not change the problem. A row with just one nonzero coordinate gives a trivial plane and is excluded. Otherwise all possibilities are
\[
            (0,1,1),\ (0,1,2),\ (1,1,1),\ (1,1,2).
\]
Indeed the nonzero elements modulo sign have classes $1,2$, interchanged by global multiplication by 2. For each type the analogue of (1) cuts out a squared-radius polygon. The checker leaves 13 cyclic types and one elementary abelian type. We must exclude three mutually compatible orbits of the **same** action; treating the three Gram matrices independently would not prove this.

## 3. Certifying incompatibility on a continuum of phases and radii

Let $w,v$ be squared-radius triples of two orbits. After rotating each coordinate plane independently, their relative phases are $\theta_1,\theta_2,\theta_3$ in turns. For each row $g$ of the finite angle group (coordinates modulo $m$), one must have
\[
           \sum_{i=1}^3\sqrt{w_i v_i}
                 \cos\big(2\pi(\theta_i+g_i/m)\big)\le\tfrac12 .
 \tag{2}
\]
All rotations here commute. For a cyclic action choose the first frequency to be 1, and restrict $\theta_1$ to an interval of length $1/m$ by changing the representative of one orbit. In the elementary abelian case the projection to the first two angle coordinates is onto (the displayed rows have $H_3\ne0$); restrict each of the first two intervals to length $1/5$. The other intervals have length one.

First the checker intersects the radius simplex with rational outer versions of the self-orbit inequalities, rounding the cosines **down**. Cover this polygon by smaller closed convex polygons if needed. To test whether radius cells $B,C$ can coexist, recursively subdivide the phase box. For a phase subbox and a group element $g$, take lower bounds $c_i$ for its three cosines, by checking the interval endpoints and whether it contains a cosine minimum. A lower bound for the left of (2) is the concave function
\[
 \sum_{c_i\ge0}c_i\sqrt{w_i v_i}+
 \sum_{c_i<0}c_i(w_i+v_i)/2 .
\]
Its minimum on $B\times C$ is attained at a pair of vertices. The sign of the second sum matters: it uses the arithmetic **upper** bound for a geometric mean multiplied by a negative cosine. If a single $g$ violates (2) strictly at every such vertex pair with this lower bound, that whole phase subbox is impossible. A cell pair is declared incompatible only if all of its phase boxes are proved impossible. An unresolved pair is left as a possible edge; it is not declared realizable.

On the radius cells, insert all possible edges, **including loops**. Three realizable orbits would give a triangle allowing repeated cell indices. For each of the 14 order-25 types the graph has no such triangle after at most two radial bisections per branch. Thus 75 is excluded. For order 37 the same self-orbit enumeration leaves six frequency types. Each is already impossible for **two** orbits with the whole radius polygon as one cell. Since a 37-symmetry of 74 points must have three active planes and no fixed points, this also rules it out without transitivity.

The checker uses rational clipping, integer square roots and outward bounds for all trigonometric evaluations. There is no reliance on a sampled search, floating-point linear-programming feasibility, or treating a failed search as an exclusion. The estimates use closed boxes, so equality at the kissing threshold is included.

## 4. The order 76 case and a flat-torus bound

Suppose now that $G$ acts transitively on 76 points. It has a Sylow 19-subgroup $P$. By [Feit–Thompson, Theorem 1](https://msp.org/pjm/1961/11-4/pjm-v11-n4-p09-s.pdf), $P$ is normal and abelian because the faithful complexified representation has degree $6$ and $19>2\cdot6+1$. Every element of order 19 requires three distinct nonzero rotation frequencies by §1, so has no fixed unit vector. A nontrivial point stabilizer in $P$ would itself contain an element of order 19. Consequently $P$ acts freely, $|P|\mid 76$, and $P=C_{19}$.

Write its three conjugate frequency pairs as a set $K$ in $\mathbb F_{19}^*/\{\pm1\}$. Normality makes $G$ permute the three real planes by multiplication on $K$. The multiplier group preserving $K$ acts freely there: a multiplier fixing a nonzero class is the identity modulo sign. Its order divides 3. Thus the orbit of the **ordered triple of plane radii** of a point has size 1 or 3. Transitivity makes all fibers equally large, so this size also divides 76. It is 1. All 76 points lie on the same flat torus of fixed radii.

For clarity, **any** kissing set on a single three-torus of radii $r_i$ with $\sum r_i^2=1$ has at most 70 points. If all $r_i\ge1/6$, lift its points periodically to $\mathbb R^3$ with period lengths $2\pi r_i$. The intrinsic distance between distinct lifted points is at least $d=\pi/3$: for differences of least angular representatives $\theta_i$, Jensen's inequality for the convex function $(\arccos t)^2$ gives
\[
 \sum r_i^2\theta_i^2\ \ge\ 
 \big(\arccos(\sum r_i^2\cos\theta_i)\big)^2\ge(\pi/3)^2.
\]
Convexity follows from $\sin\theta-\theta\cos\theta\ge0$ on $[0,\pi]$. Copies of the same point are also separated by $d$ because each period is at least $d$.

For any Euclidean $d$-separated set $Z$, the translates of $\max(0,1-2\|t\|^2/d^2)$ have sum at most 1 at every query point. Indeed, for the $k$ contributing centers the sum of squared distances to the query is at least $k^{-1}\sum_{i<j}\|z_i-z_j\|^2\ge(k-1)d^2/2$. The integral of this gauge in three dimensions is $(8\pi/15)(d/\sqrt2)^3$. Integrating over a period parallelepiped and using $r_1r_2r_3\le3^{-3/2}$ yields
\[
       N\le\frac{(2\pi)^3 3^{-3/2}}{(8\pi/15)(d/\sqrt2)^3}
          =\frac{270\sqrt{2/3}}{\pi}<71 .
\]
If one or two radii are smaller than $1/6$, drop those coordinates. Distinct projected points still have chord distance at least $\sqrt{1-8/36}=\sqrt7/3$ since the deleted squared distance is at most $8/36$. The remaining periods are at least $\pi/3$. In two dimensions ordinary disjoint disks of diameter $\sqrt7/3$ in a period cell of area at most $2\pi^2$ give $N\le72\pi/7<33$; in one dimension intervals give $N\le6\pi/\sqrt7<8$. This completes the 76-point exclusion and the theorem.

**Reproduce:** `python3 verify-kissing-six-vertex-transitive.py`. Python's standard library is sufficient. The expected output reports the prime census, six order-37 types, thirteen cyclic and one elementary abelian order-25 type, and 8,899 phase boxes. The elementary radial proof is specialized to these group orders; one-orbit optimization for commutative group codes is a classical subject, e.g. [Torezzan et al.](https://arxiv.org/abs/1205.4067). For the underlying 72-point constructions and rigidity, see [Cohn–Jiao–Kumar–Torquato](https://msp.org/gt/2011/15-4/gt-v15-n4-p11-p.pdf).