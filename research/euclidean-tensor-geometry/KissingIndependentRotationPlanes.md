# Independent rotation planes in spherical kissing codes

A rotation here is **simple**: it rotates one real two-plane, fixing its perpendicular complement pointwise. Let $M_d(a,b,c,e)$ be the largest size of a unit-vector code with all distinct pair products at most $1/2$, invariant under independent rotations on mutually orthogonal two-planes: $a$ of order 3, $b$ of order 4, $c$ of order 5 and $e$ of order 6. Its common fixed space has dimension $d$. All powers of each rotation may be used independently. The plane description is intrinsic for commuting independent simple rotations of these orders: the moving two-space of one is preserved by the other; averaging powers gives its projection onto the fixed complement, so a different invariant two-plane is either orthogonal to this moving space or equals it. We assume distinct plane factors. Set $\tau_0=0$ by convention. There is no assumption that the code is a single orbit, or that it is a lattice shell.

**Separation theorem.** For all nonnegative parameters,
\[
 M_d(a,b,c,e)=M_d(a,b,0,0)+c\,L_d+6e,\qquad
 L_0=5,\quad L_1=10,\quad L_d=15\ \ (d\ge2).
\]
In fact **every** code for the first two types of plane can be retained, without moving a single old point, while adding the indicated $cL_d+6e$ points in the larger space. Thus with order-five planes alone and $d\ge2$ the answer is **$\tau_d+15c$**, where $\tau_d$ is the ordinary kissing number; the formula does not assume $\tau_d$ is known. For example a single simple fifth rotation has an exact maximum of **255 in dimension ten** and **196,575 in dimension 26**, by the classical values $\tau_8=240$ and $\tau_{24}=196560$ ([Odlyzko–Sloane](https://neilsloane.com/doc/Me66.pdf); independently Levenshtein).

**Quarter-turn theorem.** For $b\ge1$, $0\le d\le3$ and $n=2b+d$,
\[
                  M_d(0,b,0,0)=2n(n-1).
\]
The normalized $D_n$ root configuration attains the value. For $d=0,1,2$ it is **the only equality case up to orthogonal isometry**. At $d=3$ we claim the exact value, not an isometry classification. These are sharp symmetry-restricted results; they do not identify a new unrestricted kissing number.

## Why the fifth and sixth planes separate

For a point with projection of length $\rho>0$ in an active order-$j$ plane, one of its group images changes just that coordinate by angle $2\pi/j$. Its distance must be at least one, so
\[
                \rho\ge [2\sin(\pi/j)]^{-1}.
\]
For $j=3,4$ the squared lower bounds are $1/3,1/2$. For $j=5$ the squared lower bound exceeds $2/3$ (equivalently $\cos(2\pi/5)>1/4$). Thus a point moving in any fifth plane has no projection to any other moving plane. Its other coordinates lie in the common $d$-space. For $j=6$ the radius is one and all other coordinates vanish. A single sixth plane holds at most one regular hexagon.

The [sharp single-plane theorem and explicit three-pentagon construction](https://github.com/mxym/math/blob/7a1c19f261d81db9ff40448400bf25d4bb6abf63/research/euclidean-tensor-geometry/KissingSimpleRotationsAndSeventyFiveSymmetry.md) show that a fifth plane supports at most three moving pentagons. Three require a rank-two configuration of their fixed projections; with $d=1$ there can be at most two. With $d=0$ there is at most one, since ten points cannot lie on one kissing circle. This proves the upper bound in the separation theorem. For the construction when $d=0$ take a unit pentagon in each fifth plane. When $d=1$ use the two icosahedral pentagons of heights $\pm1/\sqrt5$, radii $2/\sqrt5$ and relative phase $\pi/5$ in each plane. These heights are compatible also with either fixed pole.

For $d\ge2$ use the rigid 15-point block in each fifth plane. Its three fixed projections have length
\[
                    H=1/(2\cos18^\circ).
\]
Their directions form a coplanar triple with successive gaps $108^\circ,108^\circ,144^\circ$. The remaining coordinates lie in the new fifth plane. Any old point moving in an order-three or order-four plane has fixed projection of length at most $\sqrt{2/3}$; thus its inner product with any new point is at most $H\sqrt{2/3}<1/2$. New points from different fifth planes have cross product at most $H^2<1/2$, even if we use *the same triple* of fixed directions in all planes. Unit hexagons in new sixth planes are orthogonal to everything else. It remains only to orient the triple so that each direction is at angle at least $18^\circ$ from every point of the currently fixed code $Y\subset S^{d-1}$.

### The cap-avoidance step retains every old code

If $Y$ is empty there is nothing to prove. For $d=3$ randomly rotate the triple in the common space. Each of its three directions is individually uniform, irrespective of their dependence. As $|Y|\le12$, the chance of any bad incidence is at most $18(1-\cos18^\circ)<1$, using the area of a cap on $S^2$ and $\cos^2 18^\circ=(5+\sqrt5)/8>(17/18)^2$.

For $d\ge4$ the open $30^\circ$ caps centered on $Y$ are disjoint. If $\mu(\alpha)$ is the fraction of the sphere in one cap of angular radius $\alpha$, the failure probability is at most $3\mu(18^\circ)/\mu(30^\circ)$. Put $m=d-2$. The cap ratio is the ratio of two integrals of $\sin^m t$. The inequalities $(3/\pi)t\le\sin t\le t$ for $0\le t\le\pi/6$ imply
\[
       3\,\mu(18^\circ)/\mu(30^\circ)\ \le\ (9/5)(\pi/5)^m<1 .
\]
No assumption about the structure of an optimal fixed code is used. The elementary disjoint-cap argument is classical; compare [Jenssen, Joos and Perkins](https://doi.org/10.1016/j.aim.2018.07.001).

For $d=2$ mere averaging need not give a strict margin. Here is an exact finite reduction. Work in units of six degrees on a circle of circumference $60$. Write the fixed directions as $0=\theta_0<\cdots<\theta_{m-1}<60$ with all cyclic gaps at least $10$, so $1\le m\le6$. As the triple rotates, its bad phase centers are, up to a common translation, precisely
\[
          \theta_i+\{0,18,36\}\pmod{60}.
\]
A good phase exists exactly when these centers have a cyclic gap of at least $6$: its midpoint has distance at least $3$ from every bad center. Endpoints are permitted by the kissing inequality.

If this failed, fix the cyclic order of all $3m$ lifted centers and their integer wrap counts in such a failing configuration. Their sorted order gives non-strict difference inequalities $\theta_i-\theta_j\le z$, and all the consecutive gaps (including the wrap gap) give strict inequalities $\theta_i-\theta_j<z$, with **integer** right sides. The cyclic spacing conditions on $Y$ have the same non-strict form. Ignore the common translation by anchoring at $\theta_0$ after solving. Any directed simple cycle of these difference constraints has at most $m$ edges. If it contains a strict inequality, its total integer right side must be at least one. Therefore replacing every strict right side $z$ by $z-1/m$ leaves all cycles of nonnegative total weight. Shortest-path potentials after adjoining a zero-weight source yield a solution on $(1/m)\mathbb Z$, still strictly failing. Subtract the potential at vertex zero. The order and the wrap-gap conditions ensure that the lifted sequence represents the cyclic order even when two centers coincide.

It thus suffices to check ordered cyclic gaps $10m+v_i$ in integer units of $1/m$, with $v_i\ge0$ and $\sum v_i=m(60-10m)$. The [standard-library verifier](verify_kissing_independent_rotation_planes.py) enumerates every weak composition. For $m=1,\ldots,6$ the counts are $1,81,4186,91881,316251,1$; the minimum largest gap on those grids, in the original six-degree units, is $24,12,10,15/2,6,6$. No grid configuration has largest gap strictly less than six. We use this finite calculation only to exclude strict failure, not to assert a general formula for every continuous minimum. This completes the separation theorem in all dimensions.

## Independent quarter turns near full rank

Consider $b$ independent square planes and a common fixed $d$-space. The lower radius bound $1/\sqrt2$ allows a point to use at most two planes. A point using two has **exactly** this radius in each, no fixed component, and supplies a $4\times4$ grid of 16 points. There is at most one grid per unordered pair of planes: if there were two, choose the nearest phases independently in both coordinates. Their product is at least $\tfrac12(\cos45^\circ+\cos45^\circ)>1/2$. Points using only one plane occur in moving square orbits. We count separately the fixed points, the squares on each single plane, and the at most $16\binom b2$ grid points.

The [single-square product bounds](https://github.com/mxym/math/blob/7a1c19f261d81db9ff40448400bf25d4bb6abf63/research/euclidean-tensor-geometry/KissingSimpleRotationsAndSeventyFiveSymmetry.md#fourfold-rotation-a-product-code-for-the-moving-squares) give the facts used here: without any central square there are at most 4 or 7 square orbits in fixed dimension 2 or 3 respectively. With a central (unit-radius) square, every other square on the same plane has radius $1/\sqrt2$, relative phase $45^\circ\bmod90^\circ$, and marked unit fixed directions of pairwise nonpositive products. Thus there are at most $2d$ such others; equality is an orthoplex.

* $d=0$: there are no fixed points and at most one central square per plane, giving $4b+16\binom b2$.
* $d=1$: without a central square there are at most two squares per plane: at most one with each nonzero fixed sign, by the product bound $w_i\cdot w_j\le1-\cos\delta<1$ for their unit fixed directions. With a central square there are at most three in total. If any plane has three, its two noncentral squares have heights $\pm1/\sqrt2$, ruling out both fixed poles. Otherwise even the putative two poles only give $2+8b+16\binom b2$. The upper bound is therefore $12b+16\binom b2$.
* $d=2$: without five squares on any plane the bound is $6+16b+16\binom b2$. Five squares on a plane require its central square and four noncentral squares with fixed directions $\{\pm e_1,\pm e_2\}$. A fixed unit point must have both coordinates in $[-1/\sqrt2,1/\sqrt2]$, so only the four unit diagonals are allowed. The upper bound is $4+20b+16\binom b2$.
* $d=3$: at most seven squares fit per plane with or without a central square, and at most twelve fixed points fit. The upper bound is $12+28b+16\binom b2$.

In each case the indicated upper bound equals $2(2b+d)(2b+d-1)$. The roots $(\pm e_i\pm e_j)/\sqrt2$, $i<j$, attain it, with the coordinate planes grouped in pairs; these rotations are obvious signed coordinate permutations.

For uniqueness when $d=0,1,2$, equality in the counts forces a central square on every plane and a complete grid on every plane pair. Rotate each plane so its central square lies along the four *diagonal* unit directions in two local coordinates. A grid point of projected length $1/\sqrt2$ must then have its phase on one of the two coordinate axes: the nearest central square has product $(1/\sqrt2)\cos\delta\le1/2$ with $0\le\delta\le45^\circ$, hence $\delta=45^\circ$. Independent group motion gives the entire prescribed grid. The phases of all noncentral single squares are forced to these same axes. For $d=1$ their heights are $\pm1/\sqrt2$ on every plane. For $d=2$ the common four fixed unit diagonal points determine the fixed-space orthoplex of the four noncentral directions on *every* plane (the axes are exactly bisectors of the consecutive diagonals). All these orbits together are precisely the $D_n$ root set, with no unresolved relative phase. When $d=3$ the seven noncentral square alternative prevents drawing this uniqueness conclusion from the count alone.

These assertions concern arbitrary unions of orbits with specified independent plane rotations, unlike the one-orbit group-code problem; compare [commutative group codes](https://doi.org/10.1016/j.disc.2013.04.005). They are also different from local rigidity of the $D_n$ configuration without an assumed symmetry, as in [Cohn, Jiao, Kumar and Torquato](https://arxiv.org/abs/1102.5060). The support-count argument leaves only genuinely mixed third- and fourth-turn planes for the general reduction: an active point with $u$ third-turn and $v$ quarter-turn coordinates satisfies $u/3+v/2\le1$. It does **not** yet give the general value of $M_d(a,b,0,0)$.
