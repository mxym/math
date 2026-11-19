# Six-point Sylvester probability: the ellipse maximum

Let \(p_6(K)\) be the probability that six independent area-uniform points in a planar compact convex body \(K\) of positive area are all vertices of their convex hull.

**Theorem.** Steiner symmetrization in any line cannot decrease \(p_6\). In particular
\[
p_6(K)\le p_6(B)=1-\frac{146400\pi^2-473473}{11520\pi^4},
\]
where \(B\) is a disk; equality occurs exactly for ellipses. The disk value is [Marckert’s prior evaluation, eq. (7)](https://arxiv.org/abs/1402.3512). This is the upper comparison at six points, not a theorem on all sample sizes. The sign lemma below is proved by an exact computer-assisted calculation.

## 1. The conditional polynomial

We use the known two-comb recurrence of [Marckert and Rahmani](https://doi.org/10.1112/mtk.12110); see also its derivation and the denominator and degree bounds in the [six-point lower comparison, §§1–3](https://github.com/mxym/math/blob/59c823212883e1b26bfda23c34627a1d718d0c0b/research/sylvester-six-point-triangle-minimum/LOWER.md). Here are all the conventions needed for the upper comparison and the verifier.

Fix six increasing interior abscissas \(x_0<\cdots<x_5\), and let \(g_i=x_i-x_{i-1}>0\). Conditionally the six ordinates are independent uniforms on their vertical chords. Subtract the affine line through the two endpoint values of the lower boundary from all heights. Write \(w=(w_L,w_R)\) for the left and right widths and \(L\) for their linear interpolant. The upper and lower boundary heights, linearly interpolated between the six sites, become \(L+\sum_{i=1}^4 u_i G_i\) and \(-\sum_{i=1}^4 v_i G_i\) respectively. Here \(G_i\) is the tent vanishing at the two outside indices with slope drop one at \(x_i\); \(u_i,v_i\) are the nonnegative slope drops of the upper and of the negated lower profile. The widths are unchanged by symmetrizing.

For completeness, write \(F(w,u,v)\) for the following unnormalized probability. Condition also on the two extreme sample ordinates and split the four interior indices into those above and below their connecting chord. Each side is a one-sided concave-comb problem; add the product of the two chain volumes over all 16 splits. Average over the two independent uniform endpoint height fractions. The conditional probability given the abscissas equals \(F\) divided by the product of the four interior widths. To evaluate the comb on a subsequence with outside indices \(a,c\), choose a pivot \(j\) among its \(m\) interior indices. Multiply the two child combs by the residual cap height at \(x_j\) above the chord of the current end heights, divided by \(m\), and sum over pivots; an empty comb has volume one. The residual coefficient for a curvature site \(a<i<c\) is
\[
\frac{(x_{\min(i,j)}-x_a)(x_c-x_{\max(i,j)})}{m(x_c-x_a)},
\]
and vanishes otherwise. The endpoint labels have coefficients \({\bf1}_{a=0}(x_c-x_j)/(m(x_c-x_a))\) and \({\bf1}_{c=5}(x_j-x_a)/(m(x_c-x_a))\). Distinguish the top/bottom endpoint variables during multiplication and integrate their powers: each endpoint contributes \(\int_0^1 z^b(1-z)^c dz=b!c!/(b+c+1)!\). Convex chains above and below the original connecting chord combine into a convex polygon, up to null coincidences. These are precisely the operations implemented in `lower_exact.values`.

Set \(D=(x_5-x_0)\prod_{c-a\ge2}(x_c-x_a)>0\), where \(0\le a<c\le5\), and \(A=4!(5!)^2D F\). This is homogeneous of degree four in its ten shape variables, with integer-polynomial coefficients in the gaps. A shape term with \(e\) curvatures has homogeneous gap degree \(11+e\). Indeed no nonglobal span can occur in both disjoint comb trees; each occurs at most once within a tree, and the global span occurs at most twice. The product of the subtree sizes divides \(4!\) and each beta denominator divides \(5!\). A curvature factor has gap degree one and an endpoint factor zero; \(D\) has degree 11.

## 2. Reduce the shape cone before testing signs

Put \(s=(u+v)/2,\ t=(u-v)/2\); hence \(s_i\ge|t_i|\). For fixed gaps write
\[
\Phi(w,s,t)=A(w,s+t,s-t).
\]
Vertical reflection interchanges the two chains (and complements both endpoint fractions); thus \(\Phi\) is even under simultaneous sign reversal of \(t\). Steiner symmetrization replaces \(t\) by zero with the same \(w,s\): its chord midpoints lie on one affine line. The conditional comparison is precisely
\(\Delta(w,s,t):=\Phi(w,s,0)-\Phi(w,s,t)\ge0\).

Let \(H(w,u,v)\) denote the four-by-four negative shift Hessian of \(A\), with derivatives \(\partial_{u_i}-\partial_{v_i}\). Write \(C(w,s)=H(w,s,s)\). Since only degrees zero, two and four in \(t\) occur,
\[
\Delta(w,s,t)=\tfrac12 t^T C(w,s)t - A_4(t),                    \tag{1}
\]
where \(A_4\) depends on no shape variables other than \(t\). Define
\[
B(w,u,v)=4\,[5C(w,(u+v)/2)+H(w,u,v)].
\]
Taylor's formula for a quartic, or Euler's identity for its quadratic and quartic parts, gives the second exact identity
\[
48\Delta(w,s,t)=t^T B(w,s+t,s-t)t.                              \tag{2}
\]
Both identities concern the polynomial \(A\), already multiplied by its positive gap-dependent scale. Note that (2) does **not** require every individual coefficient matrix of \(B\) to be positive semidefinite.

**Finite sign lemma** (proved below). At every strictly positive gap vector:

1. Each of the 21 degree-two monomial coefficient matrices of \(C(w,s)\) in its six variables is positive definite.
2. Set \(w=0\) and choose for each of the four nodes just one label (either its upper or its lower curvature). In the resulting four-variable matrix \(B\), write \(M_{ii}\) for the coefficient of \(z_i^2\) and \(M_{ij}\) for the coefficient of \(z_i z_j\) for \(i<j\), where \(z_i\) is the selected curvature variable. For the two inside pairs \((1,2),(3,4)\), \(M_{ij}\) is positive definite. For each crossing pair \(i\in\{1,2\}, j\in\{3,4\}\), the matrix
\[
M_{ii}a^2+2M_{ij}ab+M_{jj}b^2                                 \tag{3}
\]
is positive definite for \(a,b\ge0\) not both zero. These are statements about the indicated matrices **after** diagonal pairing.

By (1) and part 1, \(\Delta(w,s,t)\ge\Delta(0,|t|,t)\): every degree-two scalar monomial in \(w,s\) is nondecreasing on their nonnegative orthant. If \(t\ne0\) and \(w_L>0\), the discarded coefficient of \(w_L^2\) makes the inequality strict. At \(s=|t|\), for each node at most one of \(u_i,v_i\) is positive; take these as the selected labels, with \(z_i=2|t_i|\) (choose either label at zero). The matrix in (2) at \((w,s)=(0,|t|)\) is the sum of \(M_{12}z_1z_2+M_{34}z_3z_4\) and **one half** of (3) over the four crossing pairs, with \((a,b)=(z_i,z_j)\): each diagonal occurs exactly twice. This sum is positive semidefinite, including when all \(z_i\) vanish. Thus (2) proves the reduced comparison and (1) proves the original one, strictly if \(t\ne0\) for positive endpoint widths.

## 3. Verifying the finite sign lemma

The files `upper_exact.py`, `upper_pack.cpp` and `lower_exact.py` give the full computation; no stored result array is consumed. The input to the C++ arithmetic is freshly generated by the Python stage. The Python code reconstructs all 715 coefficients of \(A\) exactly on \(g_5=1\) using its gap-degree bound 15. At the 3,876 points \((g_1,\ldots,g_4)=\mathbf1+\nu\), \(\nu\in\mathbb Z_{\ge0}^4,\ |\nu|\le15\), the combs and endpoint integrations use integer scaling with all divisions checked. Forward differences divided by the appropriate factorials give the Newton coefficients; expansion of the four falling-factorial bases in ordinary powers stays inside the same lower set. Homogeneity uniquely recovers the fifth exponent. This is unisolvent reconstruction, not a positivity test at a sample of points.

For the Hessian, deleting any ordered pair of distinct curvature occurrences from a shape monomial gives its differentiated contribution, with a minus sign for equal colors and a plus sign for distinct colors. This counts all multiplicities. Substitution \(u=v=s\) yields \(C\); for the centered part of \(B\), expand each surviving curvature factor as \((u_i+v_i)/2\). There can be at most two, so the factor 20 in \(B\) clears the possible denominators. Equality between transposed entries is checked. Color complement simultaneously on all four nodes interchanges the two labels; the program checks the equalities needed for the reduction. Thus there are 21 constant-matrix tasks for \(C\), four for the inside-pair coefficients (two relative-color choices per pair), and eight crossing-pair binary-matrix tasks. The gap-degree of an entry for a surviving shape monomial with \(e\) curvatures is \(13+e\); it is 15 in (3).

For each task test all four leading principal minors (Sylvester's criterion). Set \((a,b)=(1,y)\) in (3). Its order-\(j\) minor is homogeneous of degree \(2j\) in \(a,b\). All its \(2j+1\) coefficients, including the two pure powers needed at the endpoints, are proved to be nonzero homogeneous gap polynomials with no negative monomial coefficients. For constant matrices the same claim is checked once per minor. The total is \(25\cdot4+8(3+5+7+9)=292\) polynomials. It gives strict positivity at positive gaps, for both axes and the interior of the \((a,b)\)-quadrant as asserted.

Here is why signed integer evaluation in the C++ stage represents an **exact coefficient proof**. For a given minor use the determinant permutation expansion to bound its gap exponents per coordinate: for each permutation sum the minima and maxima of the supports of its selected entries, taking the full union over possible auxiliary powers. Minimize the lower sums and maximize the upper sums over the permutations to obtain \(l_i,h_i\). All terms are gap-homogeneous, so set any one gap to one (the checker drops a coordinate of greatest range). For the remaining four coordinates take mixed-radix strides \(m_i\) with radices \(h_i-l_i+1\). Then \(\sum_i m_i(\alpha_i-l_i)\) injects the possible exponent vectors into consecutive nonnegative slots; the omitted exponent is recovered by homogeneity. Use \(Z=2^{256}\) and evaluate the remaining four gaps at \(Z^{m_i}\) by exact multiple-precision integer arithmetic. This specialization commutes with the determinant. For binary tasks compute its polynomial coefficients in \(y\) by exact univariate Newton interpolation at \(y=0,\ldots,2j\). For each coefficient remove the common exact power \(Z^{\sum m_i l_i}\); there is no modular reduction.

If \(L\) is the largest entry coefficient \(\ell^1\) norm counted across all its gap and auxiliary powers, all true integer coefficients of a \(j\)-th order determinant have absolute value at most \(j!L^j\). The program checks this is smaller than \(Z/2\) before decoding. Every base-\(Z\) digit of the positive resulting integer is checked to be below \(Z/2\), with at least one nonzero. To see why this certifies signs even if one had started with signed coefficients, reduce modulo \(Z\): the actual least coefficient lies strictly between \(-Z/2\) and \(Z/2\), hence must equal the observed small nonnegative digit. Subtract it, divide by \(Z\), and repeat. The bound and injectivity ensure these are precisely all the ordinary monomial coefficients. No generic specialization, floating comparison, or statistical sampling is used.

## 4. Global maximum and equality

Integrating over the ordered abscissas gives Steiner monotonicity for every such body. To justify taking a maximizer, affinely normalize each body by its John ellipse so that \(B\subset K\subset 2B\). Affine maps preserve the probability; the normalized family lies in the Hausdorff-compact family of convex bodies between the two disks (Blaschke selection). Under Hausdorff convergence in this family the area-uniform distributions converge in total variation: indicators converge almost everywhere away from the null boundary of the limit, and all are bounded by the indicator of \(2B\). Thus their sixfold product laws also converge in total variation. A maximizing sequence gives an actual positive-area maximizer.

Now isotropize any maximizer by an affine change so that its centroid is at zero and covariance is the identity. It cannot improve under Steiner symmetrization in any direction. In coordinates transverse and parallel to such a direction, let \(m(x)\) be its chord midpoint ordinate. The two slope-drop lists coincide exactly when the sampled values of \(m\) are affine in the abscissas (their difference gives twice the slope drops of \(m\)). If \(m\) were not affine on the open projection interval, some triple of interior abscissas would have noncollinear midpoint heights. Extend that triple to six different interior abscissas. Noncollinearity persists on an open set by continuity of the boundary functions. Ordered samples have positive joint density there and positive endpoint widths, so the strict conditional comparison would strictly improve the maximizer, a contradiction.

Consequently \(m(x)=a x+b\). The conditional mean of the ordinate \(Y\) given the abscissa \(X=x\) is \(m(x)\). Centering gives \(b=0\), and \(0=\operatorname{Cov}(X,Y)=a\operatorname{Var}(X)\) gives \(a=0\). Thus all its parallel chords at interior abscissas are centered on the chosen axis; taking closures shows reflection invariance of the body in that axis. This holds for every direction, so the isotropic maximizer is a disk. Conversely all ellipses have the disk's value by affine invariance. This proves both the upper bound and the exact equality class.
