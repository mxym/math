# Sharp five-point kissing energy on every affine circle

Let $f(t)=t^4-t^2/4$ and $C(X)=\min_{w_i\ge0,\ \sum w_i=1}\sum_{i,j}w_iw_j f(x_i\cdot x_j)$ for a five-point unit-vector code with pairwise scalar products at most $1/2$.

**Theorem.** If the five points are contained in a single **affine** two-plane, then $C(X)\le1/4$. Equality holds exactly when that plane passes through the origin. Equivalently, in three dimensions every kissing code on a small circle has strictly smaller capacity than a code on a great circle. The same applies in any dimension, since the common normal component and the two translation directions span at most three dimensions.

This is a global result on affine-coplanar configurations: it does not require the circle to be near a great circle, the points to be equally spaced, or the weights to be uniform. The [linear-span rank-three reduction](https://github.com/mxym/math/blob/b951d2ba0c68c002beb43f9e24a55edeb3f23097/research/euclidean-tensor-geometry/KissingFivePointRankThreeReduction.md) means the unrestricted problem still requires configurations with nonzero tetrahedron volume in $\mathbb R^3$. We do not determine the unrestricted capacity here.

## 1. The angular and height variables

Write the vectors as $x_i=\sqrt{1-u}\,y_i+b$, with $b$ perpendicular to the direction plane, $\|b\|^2=u$, and $y_i=e^{i\theta_i}$ on its unit circle. Then $x_i\cdot x_j=u+(1-u)\cos(\theta_i-\theta_j)$. Projecting the code onto the unit circle in this way preserves the lower separation of $60^\circ$, since $u\ge0$. One of the five consecutive gaps is at most $2\pi/5$, and $\cos(2\pi/5)=(\sqrt5-1)/4>1/4$; its true pair cannot have scalar product $\le1/2$ if $u\ge1/3$. Thus $0\le u<1/3$.

By the [sharp doubled-angle quadrature theorem](https://github.com/mxym/math/blob/e50e33215d387d70ba4d59e325b223dcd8e46075/research/euclidean-tensor-geometry/SharpSpacingCircleQuadrature.md), there are nonnegative weights summing to one with $m_2=m_4=0$, where $m_k=\sum_i w_i e^{ik\theta_i}$. If $u=0$, then
$
 E(w,X)=1/4+(3|m_2|^2+|m_4|^2)/8
$
for arbitrary probability weights, proving $C=1/4$. We use the quadrature weights only at small nonzero heights.

## 2. An analytic bound at small positive heights

Two sharp elementary moment bounds are useful:
$
 |m_1|\le2/3,\qquad 2|m_1|^2+|m_3|^2\le1 .                         \tag{1}
$
For the first rotate the mean onto the positive real axis. For $0\le t\le1$ one has
$
 (2+11t^2-4t^4)/9-t=(1-t)(t+2)(2t-1)^2/9\ge0.
$
Apply this with $t=|\cos\theta|$; the moments of $\cos^2\theta,\cos^4\theta$ are respectively $1/2,3/8$ by $m_2=m_4=0$. For the second bound take the three orthonormal functions $e^{i\theta},e^{-i\theta},e^{3i\theta}$ in the weighted complex $L^2$ space and apply Bessel's inequality to the constant function. For example the three equally weighted directions $-\pi/3,0,\pi/3$ attain both bounds in (1).

Let $r=1-u$, $p=|m_1|^2$, $q=|m_3|^2$. Expanding $f(u+r\cos(\theta_i-\theta_j))$ and taking pair averages gives
$
 E=C_0+A p+B q,\quad
 C_0=u^4+3u^2r^2+3r^4/8-u^2/4-r^2/8,\quad
 A=ur(7u^2-6u+5/2),\quad B=ur^3 .
$
Here the first four cosine-power averages are $p,1/2,(3p+q)/4,3/8$. Since $B\ge0$ and $A-2B=ur(5u^2-2u+1/2)\ge0$, (1) gives
$
 E-1/4\le C_0+B+(4/9)(A-2B)-1/4
       =u(83u^3-100u^2+55u-2)/72 .
$
The expression is strictly negative for $0<u\le1/32$, already by $83/32^3+55/32<2$ after dropping the negative quadratic term.

## 3. Uniform weights suffice for the rest

For $1/32\le u\le1/3$ we prove the stronger finite inequality
$
   \frac1{25}\sum_{i,j=1}^{5} f\big(u+(1-u)\cos(\theta_i-\theta_j)\big)<1/4
                                                                         \tag{2}
$
for **every projected planar** tuple separated by $60^\circ$, even if its lift fails the kissing constraint. Here is the full size and specification of the interval proof.

Put $L=\pi/3$ and parameterize the consecutive gaps as $L(1+t_i)$, $0\le t_i\le1$, $\sum t_i=1$, indices modulo five. Each unordered pair occurs exactly once among the five one-step gaps and the five two-step arcs $L(2+t_i+t_{i+1})$, all in $[0,\pi]$. A search state consists of closed intervals for the five $256t_i$ with integer endpoints, and one for $960u$, starting at $[0,256]^5\times[30,320]$. Propagate the linear sum and use the dihedral symmetries of the cycle to select a lexicographically least representative: minimize the first coordinate over the full group, then the next over the stabilizer of all earlier indices. These are comparisons only, not an assumption of a symmetric configuration. For each adjacent pair of intervals also bound the sum $t_i+t_{i+1}$ by using the other three variables.

For a one- or two-step angle interval, cosine is decreasing; the two endpoint cosines are enclosed on the grid with denominator $65536$. The affine scalar product $s=u+(1-u)c$ is increasing in both $c$ and $u$ for these ranges. Round its interval outward on the same grid and bound $f(s)$ there by the maximum at its two endpoints and, if present, zero: the other two interior critical points of $f$ are minima. Round upper costs to multiples of $10^{-7}$, add five exact diagonal terms and twice the ten resulting upper bounds. This certifies every continuous point in a box whenever the total is strictly below $25/4$. Otherwise split one nonsingleton-width coordinate centrally into overlapping closed children. No numerical optimizer is used.

For cosine, the script checks an enclosure of $\pi$ by Machin's identity using alternating arctangent sums, then applies the cosine Taylor bounds through degrees 26 and 24 at outward-rounded angles. All transcendental bounds use integer numerators and denominators. The exact traversal visits 2,003 boxes: 980 accepted terminal boxes, 22 empty terminal boxes and 1,001 internal nodes. The least accepted margin in the *unnormalized* sum is $5532/10^7>0$. This proves (2); the numerical margin is only a replay check, not asserted to be optimal.

Run `node verify-kissing-five-affine-circle.js` (standard Node, no external data). The replay also checks the degree-four algebraic bound from §2. Five distinct points on a unit sphere cannot lie on a line, so their affine two-plane, when it exists, is unique.
