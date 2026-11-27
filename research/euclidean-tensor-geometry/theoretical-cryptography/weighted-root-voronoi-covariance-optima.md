# Exact Voronoi moments and shape optima for diagonally weighted root lattices

Let \(m\ge3\) and \(w_i>0\). Endow \(A_{m-1}=\{z\in\mathbb Z^m:\sum_i z_i=0\}\) with \(\|z\|_w^2=\sum_i w_i z_i^2\). Let \(V_w\) be its Voronoi cell, realized with an ordinary Euclidean metric, and \(X\) a uniform point of it. Put \(d=m-1\), \(W=\sum_i w_i\), \(H=\sum_i w_i^{-1}\), and \(D=H\prod_i w_i\).

**Theorem.** The covolume is \(\sqrt D\), the exact squared covering radius is \(R_w^2=(W-\mathbf1_{\{m\ {\rm odd}\}}/H)/4\), and \(\mathbb E|X|^2=(W+(m-2)/H)/12\). Below are exact formulas for the full covariance and all directional moments. At fixed covolume, equal weights uniquely minimize both the covering radius and every positive power mean of the covariance eigenvalues, as well as their geometric mean and maximum. The normalized covariance determinant is strictly Schur-convex in the reciprocal ratios \(a_i=w_i^{-1}/H\). The covariance is scalar exactly when all the weights are equal.

These are optima **within the weighted root family**, not among all lattices of dimension \(d\).

## 1. The weighted projected box

In physical coordinates \(y_i=\sqrt{w_i}z_i\), put \(n=(w_i^{-1/2})_i\), let \(P\) be orthogonal projection onto \(U=n^\perp\), and set \(g_i=P(\sqrt{w_i}e_i)\). Then
\[
V_w=P\prod_i[-\sqrt{w_i}/2,\sqrt{w_i}/2].
\tag{1}
\]
Indeed for real zero-sum \(h\) in the original coordinates, the weighted support function of the right side is \(\tfrac12\sum_i w_i|h_i|\). At integral \(h\) it is at most \(\|h\|_w^2/2\), so the projected box satisfies all the Voronoi inequalities. Conversely any real zero-sum \(h\) is a nonnegative sum of differences \(e_i-e_j\) oriented from its positive to its negative coordinates, by matching positive and negative masses. Their Voronoi inequalities give \(\langle h,x\rangle_w\le\tfrac12\sum_i w_i|h_i|\) on the cell, by conformity of the signs. Thus each support inequality of the projected box holds, proving (1).

The squared norm of the projection of a box corner \((\sqrt{w_i}\epsilon_i/2)_i\) is \(\tfrac14(W-(\sum_i\epsilon_i)^2/H)\). By convexity the maximum is attained at a corner, and the minimum possible absolute sign sum is the parity indicator. This proves the covering formula.

## 2. Projected lower-facet tiling and all moments

Almost every projection fiber meets the box in a segment parallel to \(n\). Its first point in the positive \(n\) direction is in one lower facet, apart from projections of facet intersections. Hence the lower-facet images tile \(V_w\) up to volume-zero overlaps. The volume of facet \(j\)'s image is
\[
\frac{w_j^{-1/2}}{\sqrt H}\prod_{i\ne j}\sqrt{w_i}
=\frac{\sqrt{\prod_i w_i}}{\sqrt H\,w_j}.
\]
Here orthogonal projection of the facet scales volume by \(|e_j\cdot n|/|n|\), the normal-angle factor. Summing gives \(\sqrt D\). The tile law conditional on index \(j\), selected with probability \(a_j=1/(w_jH)\), is
\[
-\tfrac12 g_j+\sum_{i\ne j} U_i g_i,\qquad U_i\text{ independent uniform on }[-1/2,1/2].
\tag{2}
\]
In particular the mean is zero (\(\sum_j a_j g_j=P n/H=0\)), and for \(u\in U\) all moments are given by
\[
\mathbb E e^{u\cdot X}=\sum_j a_j e^{-u\cdot g_j/2}
\prod_{i\ne j}\frac{\sinh(u\cdot g_i/2)}{u\cdot g_i/2},
\]
with value 1 for a factor of zero argument. The conditional mean and variances in (2) give a coefficient \(a_i/4+(1-a_i)/12\) for \(g_i g_i^\top\) in the covariance. Thus, as an operator on \(U\),
\[
C=\operatorname{Cov}(X)=\left.\tfrac1{12}P\operatorname{diag}(w_i+2/H)P\right|_U .
\tag{3}
\]
Since \(\|g_i\|^2=w_i-1/H\), this proves the stated trace formula. A scalar \(C\) in (3) would mean a diagonal form with entries \(b_i\) vanishes on \(U\). Testing each vector with entries \(n_j,-n_i\) at positions \(i,j\) forces \(b_i/n_i^2+b_j/n_j^2=0\) for every pair. With at least three indices it follows that all \(b_i=0\), so all \(w_i\) are equal. Conversely equal weights make (3) scalar.

## 3. Schur-convex determinant and sharp shape optima

Let \(\widehat C=C/D^{1/d}\) be the covariance scaled to unit covolume. For a positive diagonal matrix \(M\), its compression to \(U\) has determinant \(\det(M)\,n^\top M^{-1}n/H\) by the complementary principal cofactor in an orthonormal basis with final vector \(n/\sqrt H\). Formula (3) with \(w_i=1/(Ha_i)\) then gives
\[
12^d \det\widehat C
=\prod_i(1+2a_i)\sum_i\frac{a_i^2}{1+2a_i}=:\Phi(a).
\tag{4}
\]
Fix all coordinates except \(x,y\), preserving \(s=x+y\). Write \(p=xy\), \(T=\prod_{\rm other}(1+2a_i)\), \(B=\sum_{\rm other}a_i^2/(1+2a_i)\). Then
\[
\Phi/T=x^2(1+2y)+y^2(1+2x)+(1+2x)(1+2y)B
=s^2+(1+2s)B+(-2+2s+4B)p .
\]
For \(m\ge3\) there is at least one remaining coordinate, and \(a_i^2/(1+2a_i)<a_i/2\), hence \(B<(1-s)/2\). The coefficient of \(p\) is negative. Therefore any genuine transfer toward equality decreases \(\Phi\), proving strict Schur convexity by the elementary transfer criterion. In particular its minimum is unique at the equal vector. One can also see this by repeatedly averaging the largest and smallest coordinates, which converges to the equal vector.

At equal weights each eigenvalue of \(\widehat C\) is \((m+2)/(12m^{1+1/(m-1)})\); by (4) the geometric mean at any unequal weights is strictly larger. Every positive power mean and the maximum are at least the geometric mean. This proves simultaneous minimization, including of the usual normalized second moment (the trace divided by \(d\)).

For covering, fix \(W\) by common scaling. Maclaurin's inequality gives \(D=e_{m-1}(w)\le m(W/m)^{m-1}\), while \(1/H\le W/m^2\) by harmonic mean. Equality is possible only at equal weights. Thus the numerator \(W-\mathbf1_{\{m\ {\rm odd}\}}/H\) of \(4R_w^2\) is minimized there, while the normalization denominator \(D^{1/d}\) is maximized there. This proves the unit-covolume covering assertion.

## Comparison

The equal-weight projected cube and its moments are classical, e.g. [McKilliam–Subramanian–Viterbo–Clarkson on \(A_n\)](https://arxiv.org/abs/1111.6334). [Zamir–Feder](https://www.eng.tau.ac.il/~zamir/papers/lqn.pdf) study covariance in lattice quantization and isotropy at an optimal lattice. Here the unequal facet probabilities, covariance determinant and Schur-convexity give sharper simultaneous optima for this specified root family; no optimization over other lattices is asserted. The diagonal metric acts on the original zero-sum coordinates, not on their Fourier modes, and the proof does not extend as stated to several independent line-sum constraints or an instantiated cryptographic scheme. In rank one (\(m=2\)), all weights give similar lattices; the formulas still hold without the strictness assertions.

Replay: node verify-weighted-root-voronoi-covariance-optima.js (Node.js 18+, no data or dependencies).
