# Quartic stability at zero-mass planar five-point quadratures

For five unit vectors let $F_{ij}=f(x_i\cdot x_j)$, $f(u)=u^4-u^2/4$, and $C(X)=\min\{w^\mathsf TFw:w_i\ge0,\ \sum w_i=1\}$. Let $D(X)=\lambda_3+\lambda_4+\lambda_5$ for the decreasing eigenvalues of the $5\times5$ Gram matrix. This is the minimum total squared distance of the five vectors to a two-dimensional linear subspace.

**Theorem.** Let $Y$ be a planar five-point $60^\circ$ code with five distinct *unoriented* axes. In a neighborhood of $Y$, every five-point $60^\circ$ code $X$, in any ambient dimension, satisfies
$
 C(X)\le \frac14-\frac1{200}D(X)^2.                                 \tag{1}
$
Consequently $C(X)=1/4$ there exactly on the planar codes. At the previously untreated planar bases with zero quadrature weights, the exponent $2$ of $D$ cannot be decreased, even if the constant is allowed to depend on the base. The size of the neighborhood can depend on the base, not on ambient dimension. We do **not** cover planar bases containing an antipodal pair, or distant codes.

The [positive-weight result](https://github.com/mxym/math/blob/99b456fd6a91e0b0d72e8676850f686f154a0aa4/research/euclidean-tensor-geometry/KissingFivePointTransverseStability.md) gives a stronger, linear bound in $D$ at strictly positive bases, yielding (1) there after shrinking the neighborhood. The proof below concerns the genuinely different zero-weight case. Unlike the positive-weight result, it uses the separation of the perturbed code.

## 1. A plane determined by the three active points

Write $L=\pi/3$. By the [circle quadrature theorem](https://github.com/mxym/math/blob/e50e33215d387d70ba4d59e325b223dcd8e46075/research/euclidean-tensor-geometry/SharpSpacingCircleQuadrature.md), the doubled planar angles admit unique nonnegative weights with
$
 \sum w=1,\qquad \mu_2=\sum_j w_j e^{2i\theta_j}=0,\qquad
 \mu_4=\sum_j w_j e^{4i\theta_j}=0.                                  \tag{2}
$
If any weight is zero, three axes form a regular triangle of doubled nodes and take weight $1/3$ each. Their three original representatives are either an equilateral triangle or three consecutive vertices of a regular hexagon. This follows by choosing one endpoint on each of three regular axes. In the equilateral case each further point must be a midpoint of one of its three $120^\circ$ gaps, creating an antipodal pair. Thus, after an isometry and relabeling, the original angles are
$
 0,\ L,\ 2L,\ 3L+s,\ 4L+t,\qquad 0<s\le t<L.
$
Indeed the weak inequalities come from separation, and $s=0$ or $t=L$ gives repeated axes.

Now perturb the code arbitrarily subject to separation. Let $v_1=x_1,v_2=-x_2,v_3=x_3$, and take $P=\operatorname{span}(v_2-v_1,v_3-v_1)$. This plane remains nondegenerate and tends to the original plane. The three $v_i$ have **the same** normal projection $b$ onto $P^\perp$, of length $h$. In original signs write $x_i=r_i y_i+z_i$, where $y_i$ are planar unit vectors of angles $\theta_i$, $z_i\in P^\perp$, $h_i=\|z_i\|$, $r_i=\sqrt{1-h_i^2}$. Put $H=\max h_i$; every $h_i$ tends to zero at the base. Use local planar coordinates continuous near the base. All constants and small-oh estimates below refer to a sufficiently small neighborhood of this fixed base.

## 2. A positive-mass approximation with errors controlled only by the active heights

We construct weights $w\ge0$ summing to one, tending to $w^0=(1/3,1/3,1/3,0,0)$, such that for the *actual projected directions*
$
 |\mu_2|+|\mu_4|=O(h^2).                                             \tag{3}
$
It matters that this is $O(h^2)$, not $O(H^2)$: an inactive point may leave the plane while the active triangle stays exactly flat.

The original consecutive active pairs $12,23$ have scalar products $ (1-h^2)y_i\cdot y_j-h^2\le1/2$. Each of the corresponding positive angular gaps in the projection is therefore at least $L-O(h^2)$, by the local Lipschitz continuity of arccosine near $1/2$. Increase those two gaps to $L$ if they fall short, fixing the first angle and adjusting the second and third by at most $O(h^2)$, leaving the last two unchanged. Let $w$ be the unique **a priori signed** solution of (2) for these adjusted angles. It tends continuously to $w^0$ by the invertibility of the five-distinct-node trigonometric interpolation matrix. Hence the active weights stay positive.

For either inactive weight individually, its sign is unchanged if its own doubled node moves within the gap between its two neighbors while the other doubled nodes stay fixed. Indeed the corresponding cardinal polynomial is
$
 \frac{\prod_{j\ne i}\sin((\phi-\phi_j)/2)}
      {\prod_{j\ne i}\sin((\phi_i-\phi_j)/2)} ,\qquad \phi_j=2\theta_j.
$
Its uniform integral is the weight; the numerator is independent of the moving node, and the denominator keeps its sign. In the original adjusted configuration the only possibly short remaining gap is $45$: gaps $34$ and $51$ have strictly positive slack at the base. If necessary move node 4 back by the shortfall of gap $45$, a vanishing distance, keeping every gap at least $L$. The five doubled nodes remain in their original cyclic order. The circle theorem gives nonnegativity of weight 4 there, hence also before that move. To check weight 5 instead, start from the original adjusted configuration and move node 5 forward. Thus both weights of that one system are nonnegative. Undoing only the $O(h^2)$ change of the active angles in the moments gives (3). No separation assumption for the projected inactive pair was made.

## 3. Energy defect

Put $V=\sum_iw_i h_i^2$, so $V\ge(1-o(1))h^2$. For $k=1,3$ let $M_k=\sum_i w_i e^{ik\theta_i}z_i$ in the complexified normal space. We have
$
 \|M_1\|=o(1)\sqrt V,\qquad \|M_3\|^2\le V.                         \tag{4}
$
For the first estimate the active contribution is $b(w_1 y_1-w_2 y_2+w_3 y_3)$ in complex planar notation. Its factor in parentheses tends to zero because the signed active directions form a centered equilateral triangle at the base. The other contribution is bounded by $\sqrt{(w_4+w_5)V}$. The second estimate is weighted Cauchy–Schwarz.

For completeness, the planar energy equals $1/4+(3|\mu_2|^2+|\mu_4|^2)/8=1/4+O(h^4)$. With $c_{ij}=y_i\cdot y_j$, the quadratic normal change in energy is
$
 Q=\tfrac52\|M_1\|^2+\|M_3\|^2-
 \sum_iw_i h_i^2\sum_jw_j c_{ij} f'(c_{ij}).
$
This follows from $f'(\cos u)=\tfrac52\cos u+\cos3u$. The inner sum is $5/4+O(h^2)$ uniformly in $i$, using (3) and the Fourier expansion of $4\cos^4u-\tfrac12\cos^2u$. By (4), $Q\le-(1/4-o(1))V$. The elementary finite Taylor estimate in [§3 of the positive-weight proof](https://github.com/mxym/math/blob/99b456fd6a91e0b0d72e8676850f686f154a0aa4/research/euclidean-tensor-geometry/KissingFivePointTransverseStability.md) bounds the remainder in absolute value by $25H^2V$ for $H\le1/16$; its proof uses only nonnegative probability weights, not (2). Since $h^4=o(1)V$, shrinking the neighborhood gives
$
 E(w,X)\le1/4-V/8.                                                    \tag{5}
$

If $V\ge H^4$, (5) gives a defect of at least $H^4/8$. Otherwise choose $j$ with $h_j=H$ and write $P_j=\sum_iw_i f(x_i\cdot x_j)$. Using $|f'|\le7/2$ and $|x_i\cdot x_j-r_jc_{ij}|\le h_i^2+Hh_i$, the error in replacing $P_j$ by $\sum_iw_if(r_jc_{ij})$ is at most $(7/2)(V+H\sqrt V)$. The latter sum, by (3), is
$
 \tfrac38(1-H^2)^2-\tfrac18(1-H^2)+O(h^2)
 =\tfrac14-\tfrac58 H^2+\tfrac38 H^4+O(h^2).
$
Here $V<H^4$, so the total error beyond the displayed polynomial is $O(H^3)$ and $P_j\le1/4-H^2/2$ in a sufficiently small neighborhood. Take $a=H^2/4$ and mix $w'=(1-a)w+a e_j$. The diagonal cost is $3/4$, so
$
 E(w',X)\le 1/4-a(1-a)H^2+a^2/2\le1/4-H^4/8.
$
In both cases $D(X)\le \sum_i h_i^2\le5H^2$, proving (1). On the plane the circle theorem gives exactly $1/4$. The span of the original plane and the five perturbed points has dimension at most seven: embedding that span into a fixed $\mathbb R^7$ gives ambient uniformity.

## 4. Why the quartic order is necessary

At any of the zero-weight bases above, keep every point fixed except for one inactive point, which is replaced by $\sqrt{1-u^2}\,y_j+u n$ for a unit normal $n$. This is a $60^\circ$ code: inner products with that point are multiplied by a factor in $[0,1]$. The other four points span the base plane. Its Gram tail $D(X_u)$ is of order $u^2$ with positive leading coefficient. For example, in plane-plus-normal coordinates its sole small nonzero frame-operator eigenvalue has leading coefficient $1-y_j^\mathsf T S^{-1}y_j>0$ times $u^2$, with $S=\sum_i y_i y_i^\mathsf T$. Positivity follows from $S-y_j y_j^\mathsf T$ positive definite, and the coefficient follows by the Schur complement at the small eigenvalue.

At $u=0$, $F(0)$ is positive definite by the five distinct axes and the positive constant, second and fourth Fourier coefficients of $f(\cos\theta)$. Moreover $F(0)w^0=\tfrac14\mathbf1$ and the active support stays fixed, so $(w^0)^\mathsf T F(u)w^0=1/4$. The whole matrix changes by $O(u^2)$ and remains uniformly positive definite. For any competing weights $p=w^0+d$, the energy is at least $1/4-O(u^2)\|d\|+c\|d\|^2$, with $c>0$; completing the square yields $C(X_u)\ge1/4-O(u^4)$. Combined with (1) this is a defect of exact order $D(X_u)^2$, not of order $D(X_u)$.

**Replay.** Run `python3 verify-kissing-five-point-boundary.py` for rational examples of the sign test, equality at the base and sharpness along ambient lifts. The local existence and uniform estimates are established by the analytic proof, not by sampling.
