# A uniform neighborhood of the planar stratum for five-point kissing energy

Let $X$ be five unit vectors in any real Euclidean dimension with pairwise inner products at most $1/2$. Put $f(u)=u^4-u^2/4$, $C(X)=\min_{w\ge0,\ \sum w=1}\sum_{i,j} w_i w_j f(x_i\cdot x_j)$, and $D(X)=\lambda_3+\lambda_4+\lambda_5$, the sum of the three smallest eigenvalues of the $5\times5$ Gram matrix.

**Uniform near-planar theorem.** There exists an absolute $\varepsilon_0>0$ such that every such $X$ with $D(X)<\varepsilon_0$ satisfies
$
 C(X)\le 1/4-D(X)^2/200.                                             \tag{1}
$
In particular equality $C(X)=1/4$ in this range is equivalent to planarity. The power two on the Gram tail is best possible, and the result is independent of the ambient dimension. We do not give a numerical $\varepsilon_0$. A proof for the remaining compact region $D\ge\varepsilon_0$ is missing: (1) is not an unrestricted five-point capacity bound or a general kissing-number upper bound.

Earlier work proves [linear transverse stability at positive-weight, distinct-axis bases](https://github.com/mxym/math/blob/99b456fd6a91e0b0d72e8676850f686f154a0aa4/research/euclidean-tensor-geometry/KissingFivePointTransverseStability.md), then [quartic stability on the rest of the five-distinct-axis stratum, with sharp examples](https://github.com/mxym/math/blob/c92244a9327b57b18215672b7f1068d79f03ea2c/research/euclidean-tensor-geometry/KissingFivePointZeroWeightStability.md). The new part is the proof at every base with an antipodal pair, where the interpolation system becomes singular and the mass split between almost coincident axes need not be continuous in the limit.

## 1. The two antipodal cases

Set $L=\pi/3$. If a planar base $Y$ has an antipodal pair, one of the two semicircles they bound contains two of the other three points. All three intervening gaps must then be exactly $L$. After an isometry and reindexing, the angles are
$
   0,\ L,\ 2L,\ 3L,\ 4L+t,\qquad 0\le t\le L .
$
If $t=0$ or $t=L$, reorient/relabel to take $t=0$: all five points are consecutive hexagon vertices. In this case let $A=\{1,2,3,4,5\}$. If $0<t<L$, put $A=\{1,2,3,4\}$; both gaps incident to node 5 are then strictly greater than $L$. In both cases the contacts needing repair are consecutive gaps within the initial block $A$; the circular gap after that block has positive slack.

Fix a reference probability $p^0$ by giving mass $1/3$ to each of the three regular axes $0,L,2L$, dividing it equally between any repeated ends, and zero to the fifth point if it lies on another axis. Thus $c_0=\min_{i\in A}p_i^0>0$; its second and fourth circular moments vanish.

## 2. Positive weights and a self-consistent plane at a singular quadrature

Fix the base $Y$. We may work in $\mathbb R^7$, since the span of the base plane $P_0$ and the perturbed five vectors has dimension at most seven. Put $d=\max_i\|x_i-y_i^0\|$, where $y_i^0$ are the base vectors. We may assume $d>0$, the base case being known. We will shrink a neighborhood of $Y$ without further notice.

**Lemma.** There exist a plane $P$ close to $P_0$ and probability weights $w$ such that in coordinates $x_i=r_i y_i+z_i$ with $y_i=e^{i\theta_i}\in P$, $z_i\in P^\perp$, $r_i=\sqrt{1-\|z_i\|^2}$, one has
$
 \sum w_i z_i y_i^\mathsf T=0,\qquad
 |\mu_2|+|\mu_4|\le C H_A^2,\qquad
 V:=\sum w_i\|z_i\|^2\ge c_0 H_A^4/d,                               \tag{2}
$
where $H_A=\max_{i\in A}\|z_i\|$ and $\mu_k=\sum w_i e^{ik\theta_i}$. The bound $C$ may depend on the base, but not on the nearby $X$.

*Proof.* Smooth a quadrature using a parameter $\sigma>0$ to be sent to zero, and write $\rho=d+\sqrt\sigma$. In the splitting $P_0\oplus P_0^\perp$, parametrize planes by $R_B P_0$, with $R_B$ the exponential of the skew matrix whose lower-left block is $B:P_0\to P_0^\perp$ and upper-right block $-B^\mathsf T$. Compute $y_i,z_i$ in the frame $R_B^{-1}$. Initially $\|B\|\le K\rho$ with $K$ fixed below; choose any Euclidean matrix norm such as the Frobenius norm. Local continuous angular lifts have the original cyclic order. Here $H=\max_i\|z_i\|=O_K(\rho)$.

For each consecutive pair $i,i+1$ within $A$, its projected gap $g_i$ is at least $L-O(H_A^2)$: indeed $r_i r_{i+1}\cos g_i + z_i\cdot z_{i+1}\le1/2$ and the gaps are near $L$. Starting from the first angle, replace these gaps by $\max(g_i,L+\sigma)$ successively along the block. Keep any node outside the block fixed. All angle adjustments are $O(H_A^2+\sigma)$; all remaining original gaps, which had strict slack, stay greater than $L$. The modified tuple has every gap strictly greater than $L$, including when an input gap already exceeded $L+\sigma$. By [sharp spacing for the doubled-angle quadrature](https://github.com/mxym/math/blob/e50e33215d387d70ba4d59e325b223dcd8e46075/research/euclidean-tensor-geometry/SharpSpacingCircleQuadrature.md), its doubled nodes are distinct, and its quadrature weights $\widetilde w$ are positive and continuous in $B$ (for each fixed $\sigma>0$). When evaluated at the *unmodified* projected angles their moments satisfy $|\widetilde\mu_2|+|\widetilde\mu_4|=O(H_A^2+\sigma)$.

Set $\eta=(H_A^2+\sigma)/\rho$ and $w=(1-\eta)\widetilde w+\eta p^0$. For a sufficiently small neighborhood and small $\sigma$, $0<\eta<1$. Since $p^0$ annihilates the original base moments, its moments at these projected angles are $O_K(\rho)$. Thus uniformly on the ball
$
 |\mu_2|+|\mu_4|=O_K(H_A^2+\sigma),\qquad
 V\ge c_0 (H_A^2+\sigma) H_A^2/\rho .                                \tag{3}
$
The small fixed reference component controls active heights even if a particular quadrature split gives almost no mass to one end of a repeated axis.

To obtain the first identity of (2), put $\Psi(B)=\sum_i w_i z_i y_i^\mathsf T$. The continuous map $B\mapsto B+2\Psi(B)$ takes the closed ball $\|B\|\le K\rho$ into itself if $K$ is chosen sufficiently large and then $\rho$ sufficiently small. Here are the uniform estimates without differentiating any weights. The rotation expansion gives
$
 z_i=-B y_i^0+e_i,\quad \|e_i\|\le c(d+\|B\|^2),\qquad
 \|y_i-y_i^0\|\le c(d+\|B\|).
$
The constant $c$ here is independent of $K$. Equation (3) and the second-moment expression for a planar covariance matrix give $\sum w_i y_i^0y_i^\mathsf T=I/2+o_K(1)$, uniformly as $\rho\to0$ on this ball. Therefore $\|B+2\Psi(B)\|\le c' d+o_K(1)\|B\|$, for an absolute fixed $c'$ after the quadratic rotation error is absorbed into the little-oh term. Choose $K>2c'$, then shrink $\rho$. Brouwer's fixed point theorem gives $\Psi(B)=0$. For fixed small $d>0$, send $\sigma\downarrow0$ along a convergent subsequence of such planes and probability vectors. Both the zero matrix equation and inequalities (3) pass to the limit. This proves (2); continuity or uniqueness of the limiting split of mass is not needed.

## 3. Defect and uniformity

In the plane from (2), $H=O(d)$. Write $m=|\mu_2|+|\mu_4|$; (2) gives $m^2=O(d V)=o(V)$, in the sense of a uniform inequality with coefficient tending to zero as $d\downarrow0$, including $V=0$. The planar energy is $1/4+(3|\mu_2|^2+|\mu_4|^2)/8$. The quadratic normal change in energy, as in the [five-point expansion](https://github.com/mxym/math/blob/99b456fd6a91e0b0d72e8676850f686f154a0aa4/research/euclidean-tensor-geometry/KissingFivePointTransverseStability.md), is
$
 \tfrac52\Big\|\sum w_i z_i e^{i\theta_i}\Big\|^2+
 \Big\|\sum w_i z_i e^{3i\theta_i}\Big\|^2-(5/4+O(m))V
 \le -(1/4-O(m))V.
$
The first term vanishes by the plane equation, the second is at most $V$ by Cauchy–Schwarz, and the scalar radial coefficient is uniform since $4\cos^4u-\tfrac12\cos^2u$ contains only frequencies $0,2,4$. The finite Taylor remainder is bounded by $25H^2 V$ for $H\le1/16$. Thus $E(w,X)\le 1/4-V/8$ after shrinking the neighborhood.

If $V\ge H^4$ this already gives $1/4-H^4/8$. Otherwise choose a node $j$ with $\|z_j\|=H$. For $P_j=\sum_iw_i f(x_i\cdot x_j)$, replacing its arguments by $r_j y_i\cdot y_j$ costs at most $(7/2)(V+H\sqrt V)$. The resulting expression is $1/4-5H^2/8+3H^4/8+O(m)$ by the second and fourth moments. Here $m=O(\sqrt{d V})=o(H^2)$ and $V+H\sqrt V=o(H^2)$, so $P_j\le1/4-H^2/2$. Mixing $a=H^2/4$ of node $j$ into $w$, using its diagonal cost $3/4$, gives
$
 C(X)\le 1/4-a(1-a)H^2+a^2/2\le 1/4-H^4/8.
$
Since $D(X)\le \sum\|z_i\|^2\le5H^2$, (1) follows near each antipodal base.

Finally, if no uniform $\varepsilon_0$ existed there would be codes violating (1) with $D\to0$. Realize all five-tuples in $\mathbb R^5$ and take a convergent subsequence. Its limit is a planar $60^\circ$ code (not rank one, as five distinct unit points cannot lie on a line). This contradicts the local estimate at that limit, established above in the antipodal cases and in the two cited proofs otherwise. Exact equality on planar codes follows from the circle theorem. The [zero-weight examples](https://github.com/mxym/math/blob/c92244a9327b57b18215672b7f1068d79f03ea2c/research/euclidean-tensor-geometry/KissingFivePointZeroWeightStability.md) show that no power less than two works on a uniform neighborhood.

**Checks.** Run `python3 verify-kissing-five-point-uniform-stratum.py` (standard library only) for exact optimized rational lifts around both types of repeated-axis bases. The fixed point, limiting argument and compactness are analytic, not certified by finite sampling.
