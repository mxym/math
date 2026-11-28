# Sharp fivefold simple rotations, quarter-turn orbit bounds, and a symmetry restriction in six-dimensional kissing

A **simple rotation** acts in one real two-plane and fixes its orthogonal complement pointwise. All codes below consist of unit vectors whose distinct pairs have inner product at most $1/2$; the rotations need not act transitively.

1. In **any dimension**, an order-five simple rotation allows at most **three moving orbits**. If there are three, their 15-point union is unique up to isometry and spans a four-dimensional space. Counting fixed points too, the sharp maxima in ambient dimensions $2,3,4,5,6$ are respectively **5, 12, 21, 27, 39**.
2. For a simple quarter turn in dimension six, there are at most **68 points** (not claimed sharp). In dimensions four and five the sharp maxima are **24 and 40**, achieved by $D_4$ and $D_5$. The four-dimensional extremizer *within this symmetry class* is unique. These are bounds for one moving plane, not for every order-four or order-five orthogonal map.
3. A 75-point six-dimensional code **without 36 disjoint pairs of inner product below $-1/2$** has faithful geometric symmetry group of order **dividing 96**. In two of the three remaining small graph cases its order divides **48**. In particular it has no order-five symmetry, even one that rotates more than one plane, and no prime divisor other than two or three; the three-part of its order is at most three. This is a conditional restriction, **not** an exclusion of 75 points.

## Three moving pentagons: necessity and rigidity

Write $h=\pi/5$, $C=\cos h=(1+\sqrt5)/4$, $s=\sin h$. A moving orbit is a regular pentagon in a translate of the rotating plane. Its radius $\rho$ satisfies $\rho\ge r=1/(2s)$ by the edge length. Its fixed projection is $u$. Put $v=u/\rho$, $b=2s^2$, $D=2b-1$. Describe its phase modulo $2h$. If $\delta_{ij}\in[0,h]$ is the circular distance between phases of two orbits, their closest angular representatives give
\[
 \|v_i\|^2\le D,\qquad
 v_i\cdot v_j\le \frac{1}{2\rho_i\rho_j}-\cos\delta_{ij}
                 \le b-\cos\delta_{ij}<0.
\]
The last strict sign uses $b<C$.

Among three phases choose a closest pair at separation $\delta\le2h/3$. For the third phase let $\beta,\gamma$ be its distances to the first two. Then
$\cos\beta+\cos\gamma\ge C+\cos(h-\delta)$. Indeed the sum as a function on the phase circle is concave on each arc cut out by the two antipodes of the chosen phases; its minimum is at either endpoint, where the distances are $h,h-\delta$. With $z(t)=\cos t-b$, Cauchy's inequality on $v_1+v_2$ and $v_3$ now requires
\[
          [C+\cos(h-\delta)-2b]^2 \le 2D[D-z(\delta)] .
\]
The left square is of a positive quantity.

This forces $\delta=0$. For clarity set $w=\tan(\delta/2)\le\tan(\pi/12)=2-\sqrt3<.27$ and $z=C-b$. Left minus right, times $(1+w^2)^2$, is
\[
 4(z+s w-bw^2)^2-2D[(D+b-1)+(D+b+1)w^2](1+w^2).
\]
The constant is zero. Its next four coefficients satisfy respectively
$>.55,\ >-.92,\ >-3.26,\ >0$. They follow by expanding in $\mathbb Q(\sqrt5)$ and squaring the two positive quantities involving $s$; the [exact checker](verify_kissing_simple_pentagons.py) performs the comparisons. Thus for $w>0$ division by $w$ leaves more than $.55-.92(.27)-3.26(.27)^2>0$, which contradicts the necessary inequality.

At $\delta=0$ all inequalities in the chain must be equalities. The third phase is opposite on the circle modulo $2h$, hence offset by $h$; all three $\rho_i=r$. The coincident-phase fixed vectors have scalar product $b-1$ in the scaled coordinates, and their two products with the third are $b-C$. All three squared lengths equal $D$. Equality in Cauchy makes the third vector a uniquely determined negative multiple of $v_1+v_2\ne0$. Thus after two coincident phases there is only one possible distinct remaining orbit, excluding four moving orbits. The fixed Gram has rank two (its two independent directions are the sum and difference of the coincident-phase vectors). Gram uniqueness and the fixed phases prove rigidity of the moving union.

For an explicit realization let $H=\sqrt{1-r^2}$ and $A=H\cos(2h)$. In a fixed two-plane take the three footpoints
\[
             (A,1/2),\quad(A,-1/2),\quad(-H,0)
\]
and attach radius-$r$ pentagons at respective phases $0,0,h$. Here $A^2+1/4=H^2$ and $AH=r^2 C-1/2$. Within one orbit the closest product is $1/2$. Between the first two orbits it is bounded above by $A^2-1/4+r^2=1/2$, and between the third and either first orbit by $-AH+r^2 C=1/2$.

The fixed points form a kissing code in the orthogonal complement, so for $d\ge4$ the upper bound is $\tau_{d-2}+15$. We use the classical two- and three-dimensional kissing numbers $6,12$, and [Musin's four-dimensional theorem $\tau_4=24$](https://annals.math.princeton.edu/2008/168-1/p01). In dimension four add the fixed regular hexagon at phases $30^\circ+60^\circ j$ in the footpoint plane. The three footpoint directions are $72^\circ,-72^\circ,180^\circ$; their shortest angular gap to the hexagon is $18^\circ$, and $H\cos18^\circ=1/2$. In dimensions five and six add the fixed normalized $D_3$ or $D_4$ roots $(\pm e_i\pm e_j)/\sqrt2$. Cross products are at most $\max\{A+1/2,H\}/\sqrt2<1/2$. This gives 21, 27 and 39. In dimension three three moving orbits are impossible by the rank-two footpoint requirement. Two pentagons at heights $\pm1/\sqrt5$, radii $2/\sqrt5$ and offset $h$, together with both poles, give 12 (the icosahedron); in the plane a regular pentagon gives five and two distinct orbits cannot fit.

## Fourfold rotation: a product code for the moving squares

Put $d=\dim(\text{fixed subspace})$ in this section. A noncentral moving square has radius $1/\sqrt2\le\rho<1$, unit fixed direction $w=u/\sqrt{1-\rho^2}$ and phase $\theta\bmod\pi/2$. For two such squares write $\delta\in[0,\pi/4]$ for nearest phase separation. Then
\[
            w_i\cdot w_j\le 1-\cos\delta .
\]
In fact the unscaled constraint gives upper bound $(1/2-\rho_i\rho_j\cos\delta)/\sqrt{(1-\rho_i^2)(1-\rho_j^2)}$. It is nonincreasing in each radius: the derivative in $\rho_i$ has the sign of $\rho_i/2-\rho_j\cos\delta\le0$. Evaluate at both minimum radii. Conversely these product-code constraints are sufficient at the minimum radii, including the within-square angle.

Let $P_l^{(d)}$ be the normalized spherical zonal polynomials on $S^{d-1}$, using Chebyshev $T_l$ for $d=2$. Each product kernel $P_l^{(d)}(w_i\cdot w_j)\cos(4k(\theta_i-\theta_j))$ is positive semidefinite by the two addition formulas and the entrywise product theorem. The [small rational certificates](verify_kissing_simple_square_product.py) yield the following **upper bounds** on the count of noncentral square orbits:

| fixed dimension $d$ | 2 | 3 | 4 | 5 |
|---|---:|---:|---:|---:|
| maximum permitted by the certificates | 4 | 7 | 11 | 16 |
| Bernstein cells | 9 | 33 | 11 | 37 |

Explicitly each file row gives integers $c_{lk}\ge0$ divided by $10^7$ and a rational $\varepsilon$. The polynomial $1-\varepsilon+\sum c_{lk}P_l^{(d)}(t)T_{4k}(z)/10^7$ is nonpositive on the off-diagonal domain $z=\cos\delta\in[1/\sqrt2,1],\ -1\le t\le1-z$. The verifier enlarges its $z$ interval down to $.707106$, substitutes $z=.707106+(1-.707106)y$, $t=-1+(2-z)x$, and bounds its exact tensor Bernstein coefficients on $[0,1]^2$. The product code size is at most $1+\sum c_{lk}/[10^7(1-\varepsilon)]$, strictly below the next integer in every column. In fixed dimension four the rational bound is $117070007/9900000<12$.

At most one central square ($u=0$) can occur. If it does, every other square must have exactly the minimum radius $1/\sqrt2$ and phase offset $\pi/4$, since $\rho\cos\delta\le1/2$. All resulting fixed directions have pairwise nonpositive inner products, so there are at most $2d$. One elementary proof is to sum $t^2+t$ over their ordered pairs: the off-diagonal terms are nonpositive, $\sum t\ge0$ and the frame trace bound gives $\sum t^2\ge M^2/d$; thus $M\le2d$. Equality forces an orthoplex, since off-diagonal entries are then $0$ or $-1$ and the sum of the vectors is zero.

In ambient dimension six the noncentral-only case gives $24+4(11)=68$; a central square gives at most $24+4(1+8)=60$. Dimension five gives at most $12+4(7)=40$ in either case. Dimension four has at most $6+4(4)=22$ unless a central square and four noncentral ones occur. In that case the four fixed directions form the signed coordinate axes in a plane. Any unit fixed point must have both coordinate magnitudes at most $1/\sqrt2$, so at most four fixed points occur, precisely the diagonal four at equality. The normalized $D_4$ and $D_5$ roots realize 24 and 40 under rotation of one coordinate plane by $\pi/2$. This also identifies the indicated four-dimensional equality case without assuming uniqueness of arbitrary 24-point codes.

## Consequence for all symmetries of a matching obstruction

Consider only the finite permutation group induced by isometries on the span of the code; invisible motions of unused ambient dimensions are not symmetries counted here. In either [surviving 75-point template](https://github.com/mxym/math/blob/0706c1cce4601412e8c9e9c2ffb4f4066a11cde8/research/euclidean-tensor-geometry/KissingSixTwoNineGraphs.md), the seven- or nine-component is unique at its size. On the seven-cycle the image has order dividing two: two distinct reflections would generate a nontrivial cycle rotation, excluded by the [strict noncirculant Gram theorem](https://github.com/mxym/math/blob/3a815c47958df290d042f9e0e9976c5aa2093fbf/research/euclidean-tensor-geometry/KissingSixSevenComponentAsymmetry.md). On the $\theta(3,3,4)$ graph the image divides four (exchange the equal paths and/or reverse their endpoints). On the specified $K_4$ subdivision it divides two: the length-four edge and the opposite length-one edge are distinguished, and the two length-two edges distinguish one matching between their ends.

The kernel $K$ fixes the small component pointwise. Seven distinct kissing points cannot fit in a plane, so $K$ embeds in $O(3)$ on the orthogonal complement of the span they generate (pad with trivial coordinates if needed). The determinant-positive part $K_+$ has index at most two. Every nonidentity element of $K_+$ is a simple rotation on the full span. A simple rotation of order six supports only a single moving hexagon of radius one plus fixed points, at most $6+24=30$ in dimension six; of order seven or more it cannot move even one code point, because the regular orbit chord is at most $2\sin(\pi/7)<1$. The preceding bounds 68 and 39 exclude orders four and five for a 75-set. Therefore every nonidentity rotation in $K_+$ has order two or three.

For completeness this implies $|K_+|$ divides 12 without requiring the finite rotation-group classification. For $M=|K_+|>1$, count nonidentity-rotation/fixed-pole incidences on the ordinary $2$-sphere in the three-coordinate representation. Each rotation has two poles. A pole stabilizer is cyclic, of order $s_i$ equal to two or three. Summing over pole orbits yields $\sum_i(1-1/s_i)=2-2/M$. With two orbits this gives $M=2$ or $3$ (the mixed pair would not give an integer); with three it gives $M=4,6,12$ for $(2,2,2),(2,2,3),(2,3,3)$. One or four orbits are impossible. Thus $|K|\mid24$. Multiplying by the component image orders proves the claimed divisibility. The argument makes no assumption that the original 75 points are globally point-transitive.

**Replay:** run `python3 verify_kissing_simple_pentagons.py` and `python3 verify_kissing_simple_square_product.py` with standard Python. The pentagon proof and the product-kernel matrices use no numerical optimizer in verification.
