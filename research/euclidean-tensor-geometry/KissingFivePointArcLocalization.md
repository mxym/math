# Localization of any five-point energy counterexample to a short projective pentagon

Let $f(t)=t^4-t^2/4$ and $C(X)=\min_{w\ge0,\ \sum w_i=1}\sum w_i w_j f(x_i\cdot x_j)$ for a five-point $60^\circ$ code. If $C>1/4$, the pairs with scalar product strictly below $-1/2$ form a five-cycle: both this graph and its complement are triangle-free. A strong triangle would have negative squared norm of the sum; an independent triple, given equal weights, has energy at most $1/4$. Label the cycle $1,\ldots,5$, put $s_i=-x_i\cdot x_{i+1}$, $\alpha_i=\arccos(s_i)$, and $L=\sum_i\alpha_i$. Weak chords have scalar products in $[-1/2,1/2]$. Each $\alpha_i$ is the length of a short arc between signed representatives; the complete walk joins $x_1$ to $-x_1$, so $L\ge\pi$.

**Results.**
1. In *any* ambient dimension, $L\ge49\pi/48=183.75^\circ$ implies $C(X)\le1/4$. The exact continuous box certificate is described below.
2. Throughout the closed cycle cell $1/2\le s_i\le1$, $|x_i\cdot x_{i+2}|\le1/2$, if one $s_i=1/2$, the sharp upper bound is $1/4$, and equality forces all points into one plane. If $s_i=1$, another $s_j=1/2$, so the same conclusion holds.
3. Writing $D=\lambda_3+\lambda_4+\lambda_5$ for the Gram tail, one has $D\le (16/3)(L-\pi)$ on the closed cycle cell, with angles in radians. Thus the short path length really controls planarity, not just an abstract parameter.

Together with the [uniform near-planar bound](https://github.com/mxym/math/blob/a2019b76cbe115d92a9328a507ed8b66092ac749/research/euclidean-tensor-geometry/KissingFivePointUniformPlanarStratum.md) and the [global rank reduction](https://github.com/mxym/math/blob/b951d2ba0c68c002beb43f9e24a55edeb3f23097/research/euclidean-tensor-geometry/KissingFivePointRankThreeReduction.md), a counterexample, if any, can be chosen in three dimensions, strictly away from both edge-strength endpoints and with path length strictly between $\pi$ and $49\pi/48=183.75^\circ$. The two near-boundary exclusions obtained by compactness are not given effective constants. We have not proved $C\le1/4$ throughout this remaining region.

## Path length and planar rank

Use the signed walk $y_0=x_1,\ y_1=-x_2,\ y_2=x_3,\ y_3=-x_4,\ y_4=x_5,\ y_5=-x_1$. The distance $\gamma=d(y_0,y_2)$ lies in $[\pi/3,2\pi/3]$ by the weak chord. Use the plane spanned by $y_0,y_2$. Either endpoint pair $(a,b)=(y_0,y_2)$ or $(y_2,y_5)$ spans this same plane and has $\sin^2 d(a,b)\ge3/4$. For any unit $y$, let $\ell=d(a,y),\ r=d(y,b),\ t=d(a,b)$, and $v=(\ell+r+t)/2$. Then
$
 \|\operatorname{proj}_{\operatorname{span}(a,b)^\perp} y\|^2
 =\frac{\det\operatorname{Gram}(a,b,y)}{\sin^2t}
 =\frac{4\sin v\sin(v-\ell)\sin(v-r)\sin(v-t)}{\sin^2t}
 \le\tfrac83(\ell+r-t).
$
The determinant identity follows by multiplying the cosine addition formulas; the bound also follows by taking absolute values of the first three sines and using $|\sin(v-t)|\le(\ell+r-t)/2$. If $e_1,e_2$ are the respective path excesses of the segments $y_0\to y_2$ and $y_2\to y_5$, then $e_1+e_2=L-\pi$. The excess for $y_1$ is at most $e_1$; each of $y_3,y_4$ has excess at most $e_2$. The total normal squared length is at most $(8/3)(e_1+2e_2)$, proving statement 3.

## Rigidity at either edge-strength endpoint

Take $x_5\cdot x_1=-1/2$. The uniform measure on $x_1,x_3,x_5$ has energy at most $1/4$. If $C=1/4$ then this measure is optimal, and the two weak products $p=x_1\cdot x_3,\ q=x_3\cdot x_5$ must each belong to $\{0,\pm1/2\}$, as all three off-diagonal terms are nonpositive and $f$ vanishes there only at these numbers. The average potential $\sum_iw_i f(x_i\cdot x_j)$ at either outside point is at least $1/4$, by differentiating along mixing in that point.

If $p\le0$, put $u=-x_1\cdot x_2,\ v=-x_3\cdot x_2$, so $u,v\ge1/2$. The Gram determinant gives $u^2+v^2-2p u v\le1-p^2$, hence $u^2+v^2\le1$. With each square at least $1/4$, convexity on this truncated triangle gives $f(u)+f(v)\le3/8$ (the largest vertex value is at squares $1/4,3/4$). The third contribution to the potential at $x_2$ is nonpositive. Thus that potential is at most $1/8$, a contradiction. So $p=1/2$; using $x_4$ instead gives $q=1/2$. Consequently $\|x_1-x_3+x_5\|=0$, and these points give the three regular axes in their plane. Their uniform potential at any unit point of height $h$ above the plane is
$
 \tfrac38(1-h^2)^2-\tfrac18(1-h^2)=1/4-5h^2/8+3h^4/8,
$
strictly below $1/4$ for positive $h$. Hence the outsiders also lie in the plane. If $s_1=1$, then $x_2=-x_1$, and the weak bound $x_1\cdot x_3\le1/2$ forces $s_2=1/2$.

Compactness now separates every putative $C>1/4$ code from these endpoints *uniformly*: otherwise a convergent subsequence would have $C\ge1/4$ at an endpoint in the closed cell and would limit to a planar code. The [uniform near-planar theorem](https://github.com/mxym/math/blob/a2019b76cbe115d92a9328a507ed8b66092ac749/research/euclidean-tensor-geometry/KissingFivePointUniformPlanarStratum.md) rules out such a subsequence. The same theorem and statement 3 separate it uniformly from $L=\pi$.

## Exact certificate for the region $L\ge49\pi/48$

Run `node verify-kissing-five-point-arc-localization.js` with no input. The search certifies continuous boxes, not grid points. Write $a_i=3K\alpha_i/\pi$, with $K=4096$. Its initial box covers $0\le a_i\le K$; the long-arc cutoff is $\sum_i a_i\ge12544$. In addition $a_i+a_{i+1}\ge K$: the lifted two-step endpoints have weak scalar product $\le1/2$, so their separation is at least $60^\circ$. The code propagates these six linear inequalities into lower endpoints and fixes a lexicographically minimal labeling using the dihedral group. Splits at integer midpoints cover both closed children; an inconclusive terminal box would produce a failure, not acceptance.

For a weak chord $(i,i+2)$, the signed two-step path gives the lower scalar-product bound $\cos(\alpha_i+\alpha_{i+1})$. The other three steps have opposite parity and give the upper bound $-\cos(\alpha_{i+2}+\alpha_{i+3}+\alpha_{i+4})$. Both arc sums are at most $\pi$, so outward interval evaluation suffices. Intersect the resulting bounds with $[-1/2,1/2]$. All cosines are bounded on a grid of denominator $B=65536$, using degrees 24 and 26 of the cosine Taylor series at enclosing rational angles. An interval of width $10^{-15}$ for $\pi$ is first certified via Machin's identity and alternating rational arctangent sums.

**Ordinary mass certificate.** Given a nonnegative integer vector $W$ of sum 360, use upper endpoints for the costs $f$ (including zero as a possible local maximum) and exact diagonal $3/4$. The table uses integer ceilings on a scale $10^7$. For a strong arc the upper endpoint cost at $a_i=\mathrm{lo}_i$ can be reduced linearly as $a_i$ grows:
$
 -\tfrac d{d\alpha}f(\cos\alpha)=\sin(2\alpha)(3/4+\cos2\alpha)\ge0.
$
The minimum of this derivative magnitude on any subinterval of $[0,\pi/3]$ is at an endpoint: its derivative has sign $4\cos^2(2\alpha)+(3/2)\cos(2\alpha)-2$, with one zero for $\cos2\alpha\in[-1/2,1]$, a maximum of the magnitude. Round the two endpoint slopes downward after converting to angular grid units. Writing $\delta_i=a_i-\mathrm{lo}_i\ge0$, every remaining lower bound on a pair sum or the full sum has the form $\sum_{i\in J}\delta_i\ge t$. A nonnegative multiplier at most each remaining slope on $J$ gives a guaranteed additional cost reduction equal to that multiplier times $t$; subtract its slope contributions before using another constraint. Every accepted ordinary certificate thus bounds the trial energy by $1/4$ over the whole box.

**Mixed mass and Gram certificate.** Some boxes need correlations between the weak chords. Store all ten off-diagonal coordinates as $\xi=B G_{ij}$. On each current interval compute an affine upper bound $b_{ij}+s_{ij}\xi$ for $10^7 f(\xi/B)$: on a single sign outside $|\xi/B|<0.21$ take a chord of the convex polynomial, rounding both endpoint values up and raising the integer intercept enough for the selected integer slope. Otherwise take the larger endpoint cost and, if applicable, zero (other interior critical points are minima). For integer probability numerators $W_\nu$ of sum 420, this gives affine majorants $H_\nu(\xi)$ on $E(W_\nu/420,G)-1/4$, with a fixed positive normalization. All of these must be positive in a counterexample. In addition $\langle V^\mathsf T V,G\rangle\ge0$ for every integer matrix $V$. Thus a cell is excluded if for some nonnegative rational multipliers $m_\nu$,
$
 \max_{\xi\ \mathrm{in\ box}}\left(
 \langle V^\mathsf T V,G\rangle+\sum_\nu m_\nu H_\nu(\xi)\right)<0.
$
The maximum selects one endpoint per coefficient and is evaluated in **BigInt** after clearing positive denominators. Numerical eigensolvers and projected iterations merely propose candidate integer factors, mass vectors and multipliers. Reused cuts are re-certified with the actual bounds of the current box. None of the floating-point guesses can accept a mixed cut without a strict integer check.

The traversal visits 829,575 boxes: 414,780 energy-certified leaves (238,864 by the mixed test), eight empty leaves, and 414,787 internal nodes. The cutoff is a proved sufficient condition, not claimed optimal.
