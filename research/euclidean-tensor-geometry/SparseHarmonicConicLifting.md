# A sparse single odd harmonic relation is already a full moment relation

**Sparse lifting theorem.** Let $d\ge6$ and let $k$ be positive and odd. Suppose $r\le3k-1$ distinct real projective directions are represented by nonzero real vectors $x_i$, with nonzero scalar weights $c_i$, such that
$$
                 \sum_i c_i H(x_i)=0
$$
for every homogeneous harmonic polynomial of **the single degree $k$**. Then this identity holds for **every homogeneous polynomial of degree $k$**, not just the harmonic ones. The directions lie on a reduced projective curve of degree at most two: a plane conic or two lines (possibly skew). In particular their real linear span has dimension at most four. Weights may be complex; the projective directions must be real.

**Kissing consequence.** In any $d\ge6$, a non-antipodal $60^\circ$ spherical code of one odd harmonic index $k\ge5$ has **at least $3k$ unpaired points**. The same bound holds in any real dimension if *all* odd indices through $k$ vanish. This strengthens the [previous $2k+2$ count](KissingSingleHarmonicObstructions.md). A six-dimensional kissing code with **any single odd harmonic index $k\ge27$ is necessarily antipodal**; a seven-dimensional one is antipodal for any single odd $k\ge45$. These are recognition criteria, not unrestricted cardinality bounds.

We use [Picoco, Theorem 3.1](https://arxiv.org/pdf/2201.01665): a set of distinct complex projective points with the degree-$k$ Cayley–Bacharach property and size at most $3k-1$ lies on a reduced degree-two curve. The Cayley–Bacharach property means that every degree-$k$ polynomial vanishing at all but one point vanishes at the last. A full-support weighted relation on all homogeneous evaluations implies that property. Picoco assumes **all homogeneous tests**; moving from harmonic to homogeneous tests is the point of the first theorem here.

## 1. Six real directions seen in a complex plane

Identify an oriented Euclidean six-space with $\mathbb C^3$ by three orthogonal complex coordinate forms $L$. Holomorphic polynomials in $L$ pull back to harmonic polynomials. For a generic orthogonal complex structure, any prescribed finite list of distinct real projective directions remains projectively distinct over $\mathbb C$: for a given independent pair put the pair's real span in the first two real coordinate directions, then use genericity. This works in either orientation. For such an identification Picoco's theorem in $\mathbb P^2$ gives a complex conic through all the projected points. Consequently the determinant of the six quadratic monomial evaluations at any selected six images is zero. By continuity it is zero for **every** orthogonal complex identification, including nongeneric ones.

Here is the key elementary linear-algebra statement:

> If six real basis vectors of $\mathbb R^6$ have complex projective images on a conic for every orthogonal complex identification (in the determinant sense), the six vectors are pairwise orthogonal.

Split the basis arbitrarily into two triples with real spans $A,B$; thus $A\cap B=0$. We show that if $A$ is not perpendicular to $B$, we can find an identification for which there is no conic. Choose a real two-plane $P\subset A$, neither perpendicular to $B$ nor equal to the span of any two members of the first triple. Such planes are generic under the nonorthogonality hypothesis. Write $V=P^\perp$, $A=P\oplus\mathbb R a$ with $a$ a unit vector in $V$. Give $P$ a quarter-turn with complex coordinate $\alpha$ and equip $V$ with a variable orthogonal complex structure $J'$. The first three points then project to three **distinct** points on one complex projective line: the only complex line (real two-plane) contained in $A$ is $P$, since $A\cap JA=P$. The inverse image of their projective line is the real space $P\oplus\operatorname{span}(a,J'a)$.

For each basis vector $b$ of the other triple its $V$-projection $v$ is not parallel to $a$, since $b\notin A$. A generic $J'$ keeps $v$ outside $\operatorname{span}(a,J'a)$: the possible $J'a$ fill the unit two-sphere perpendicular to $a$ in $V$, and at most two choices are forbidden. We next show that we may **also** make the images of that triple complex linearly independent.

Let $b_1,b_2,b_3$ be its basis, $v_j=\operatorname{proj}_V b_j$ and $c_j=\alpha(b_j)$. The $v_j$ are real independent because $B\cap P=0$; not all $c_j$ are zero since $B$ is not perpendicular to $P$. Thus
$$
        \xi=c_1v_2\wedge v_3-c_2v_1\wedge v_3+c_3v_1\wedge v_2
$$
is nonzero in $\bigwedge^2 U_{\mathbb C}$, where $U=\operatorname{span}_{\mathbb R}(v_1,v_2,v_3)$. For the complex area form $\beta$ on the four-space $V$ the determinant of the second triple is $\beta(\xi)$. The restrictions of the possible $\beta$ span the complex dual of $\bigwedge^2 U$. To check it explicitly, take orthonormal coordinates $u_1,u_2,u_3$ on $U$ and $u_4$ normal in $V$ (here $u_j$ also denote the coordinate forms). The form $(u_1+i u_4)\wedge(u_2+i u_3)$ and its two cyclic permutations of the first three coordinates all come from complex structures with the **same** orientation. In the basis $u_1\wedge u_2,u_2\wedge u_3,u_3\wedge u_1$, their restrictions have rows $(1,0,-i),(-i,1,0),(0,-i,1)$ with determinant $1+i$. Hence nonvanishing holds on a nonempty open set, and simultaneously with the three preceding generic avoidance conditions (or perturb a good complex basis in its connected orientation component).

For that identification the second triple is off the first line and noncollinear. A conic through three distinct points of the first line must contain the line as a component, leaving only one further line for all three off-line points. This is impossible. Thus $A\perp B$ for every partition into triples; placing any selected pair on opposite sides shows it is orthogonal. The exception is genuine at the determinant level: for an orthonormal basis $e_j$, $\sum_jL(e_j)L(e_j)^t=0$ by isotropy, so the six quadratic evaluations are dependent for every identification.

## 2. Lifting from harmonic to full moments

First work in dimension six. If the directions span the space, any independent two can be extended to a basis chosen among them. The determinant in §1 vanishes on that basis, so the two must be orthogonal. The distinct projective directions are then **exactly six orthogonal axes**. But these six evaluations admit no full-support relation of odd harmonic degree: in orthonormal coordinates the harmonic $\operatorname{Re}((z_a+\mathrm i z_b)^k)$, with $a\ne b$ and $z_a,z_b$ real coordinate functions, is nonzero precisely on the $a$th axis among the six. This contradicts its nonzero weight.

In $d>6$, if the real rank is at least six, project orthogonally onto a generic six-space preserving some independent six and all independent pairs. These finitely many requirements follow from nonvanishing Gram minors; the projections need not have unit norm. Harmonics on this space pull back to harmonics on the ambient space, so the same full-rank contradiction applies. Thus in all cases the original support has rank at most five, strictly less than $d$.

On a proper linear subspace every homogeneous polynomial $p(u)$ extends to an ambient harmonic polynomial of the same degree. In one perpendicular coordinate $t$ take
$$
           H(u,t)=\sum_{j=0}^{\lfloor k/2\rfloor}
                   \frac{(-1)^j t^{2j}}{(2j)!}\Delta_u^j p(u).
$$
The $t$-Laplacian cancels the $u$-Laplacian term by term; restrict to $t=0$. Full homogeneous balance on the support is proved. Applying Picoco again to these **original** directions yields the degree-two curve conclusion (the rank-one or rank-two cases are immediate). A complex plane conic spans at most a projective plane, two complex lines at most a projective three-space, giving real rank at most four. For unit vectors homogeneous balance also gives every odd moment below $k$ by multiplying by a power of the squared norm.

## 3. Ten is a cap on the unpaired kissing points on a conic

Remove antipodal pairs. On one real projective line there are at most five remaining directions: six points on its great circle with gaps at least $60^\circ$ form a regular hexagon, with antipodes. A complex line containing two real points is their real line complexified, so two lines contribute at most ten. For an irreducible plane conic with at least five real points, the plane is real (three points are noncollinear), and the conic is real, since otherwise its conjugate is a distinct conic with more than four intersection points. If there are fewer than five there is nothing to bound. Its nonsingular real ternary quadratic form is indefinite. After orthogonal diagonalization and overall sign its equation is $\lambda_1 x^2+\lambda_2 y^2=\lambda_3 z^2$ with all $\lambda_i>0$.

Each of the two lifts to the unit sphere is a strictly convex oval in an open hemisphere: in the chart $(x/z,y/z)$ it is an ellipse. Any ordered cyclic subset of at least three points on one oval is a convex spherical polygon. Its perimeter is **strictly** less than $2\pi$. Indeed a uniformly random great circle crosses a shorter edge of spherical length $\ell$ with probability $\ell/\pi$, by the angle between the two endpoint hemispheres of normals. It crosses the convex polygon boundary at most twice outside null degeneracies (use the same planar chart), and a positive measure of great circles misses the compact polygon entirely, as it is in an open hemisphere. Summing the crossing probabilities gives the strict inequality. A $60^\circ$ code therefore has at most five points on each oval, ten in total.

If a nonempty residual of odd index $k\ge5$ has $r\le3k-1$, §§1–2 put it on such a curve, so $r\le10$. But it has at least $2k+2\ge12$ points: through $2k+1$ the [target-isolating line argument](OddHarmonicParitySpectrum.md) puts all points on a great circle, where at most five survive, and even a nonempty harmonic relation needs at least $k+2\ge7$. This contradiction proves $r\ge3k$. Under simultaneous odd balance one starts directly with full homogeneous balance, so this last argument works also for $d<6$.

By [Tomar's general upper bounds](https://www.mefyi.com/papers/kissing-numbers-five-seven/) a six-dimensional code has at most $76$ points and a seven-dimensional one at most $132$. Thus $3k>N$ forces antipodality at the cutoffs stated above. Combined with the [single-index certificate at 25](KissingSingleHarmonicObstructions.md), **each odd index at least 25 now suffices for the 72-point ceiling in six dimensions** (at 25, antipodality is not asserted). In particular at the previously unresolved index 27 equality is necessarily the antipodal $E_6$ code. The seven-dimensional recognition statement at 45 is about full antipodality, stronger than just its $126$-point ceiling.

The argument is analytic. The companion [exact test](verify-sparse-harmonic-conic.py) checks the six-coordinate linear algebra on orthogonal and sheared integer frames, including its orthogonal exception; it is not a substitute for Picoco's theorem or the genericity argument.
