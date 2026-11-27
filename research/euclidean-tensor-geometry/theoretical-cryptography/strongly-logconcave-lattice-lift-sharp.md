# The sharp curvature of a uniform-modulo-lattice lift on the line

A probability density on \(\mathbb R^n\) is \(\alpha\)-strongly log-concave if \(f(x)e^{\alpha\|x\|^2/2}\) is log-concave; this definition permits zeros and agrees with the Hessian bound for smooth positive densities. A *uniform lift* of \(\mathbb R^n/L\) is such a density whose reduction modulo \(L\) is uniform.

**The optimal curvature on \(\mathbb R/\mathbb Z\) is \(\alpha_* = 8\log 2\).** In the class of all densities it has a unique extremizer up to translation: a compactly supported profile assembled from a Gaussian central piece and its complementary folded tails. In the smooth strictly positive class \(8\log2\) is a supremum but is not attained. No symmetry assumption is needed for the upper bound or uniqueness. Near equality one has quantitative closeness to the profile after translating its mode. In higher dimension this determines the exact supremum for orthogonal rectangular lattices and improves the general necessary upper bound in terms of the shortest dual vector.

This is a sharp special case and obstruction for the lift considered by [Letwin–Reis–Rothvoss, arXiv:2610.29238 v2](https://arxiv.org/abs/2610.29238). Their Theorem 1.1 gives \(2\pi/e\) for all lattices with weakly stable duals, with a determinant-based converse. We do not claim to improve their universal lower constant or to determine the best lift on all lattices.

## 1. The one-dimensional upper bound from half-period sampling

First suppose \(f\) is continuous, allowing zeros. Strong log-concavity implies a Gaussian tail envelope (take a supporting slope of the convex residual potential at any interior point). It follows both that \(f\) has a mode and that \(\sum_{k\in\mathbb Z}f(x+k)=1\) holds everywhere by continuity and locally uniform convergence, since uniformity gives it almost everywhere. Translate a mode to zero. Writing \(V=-\log f\) with \(V=+\infty\) outside its support, \(0\) is a subgradient at the mode, so the convex function \(V(x)-\alpha x^2/2\) also has its minimum at zero. Hence \(g(x)=f(x)e^{\alpha x^2/2}\) is nonincreasing along each ray from zero, and for \(j\ge0\),
\[
 f(\pm(j+1/2))\le e^{-\alpha(j/2+1/8)}f(\pm j).
 \tag{1}
\]
The argument works at support endpoints by continuity. Compare the two modular fibers:
\[
 1=\sum_{j\ge0}\bigl[f(j+1/2)+f(-j-1/2)\bigr]
   \le e^{-\alpha/8}\bigl(2f(0)+\sum_{j\ge1}[f(j)+f(-j)]\bigr)
   =e^{-\alpha/8}(1+f(0))\le 2e^{-\alpha/8}.
 \tag{2}
\]
Thus \(\alpha\le8\log(1+f(0))\le\alpha_*\); full support makes the last inequality strict because the integer fiber has positive mass away from zero.

For a density not assumed continuous, convolve with an independent centered Gaussian of variance \(\sigma^2>0\). Uniformity is preserved, since addition by an independent variable preserves a uniform residue. The convolution is smooth, strictly positive, and has strong log-concavity parameter at least
\[
 \alpha_\sigma=\frac{\alpha}{1+\alpha\sigma^2}.
 \tag{3}
\]
To prove (3) directly, write \(f(y)=e^{-\alpha y^2/2}h(y)\) with \(h\) log-concave. Completing the square in the convolution expresses it, up to a constant, as
\[
 e^{-\alpha_\sigma x^2/2}\int h(y)
     \exp\!\left[-\frac{\alpha+\sigma^{-2}}2
           \left(y-\frac{x}{1+\alpha\sigma^2}\right)^2\right]dy .
\]
The integrand is jointly log-concave, so the integral is log-concave by [Prékopa's marginal theorem](https://acta.bibl.u-szeged.hu/14411/). Apply the continuous upper bound and let \(\sigma\downarrow0\). This proves the universal one-dimensional upper bound.

## 2. Equality, sharp smoothing, and stability

Define
\[
 f_*(x)=
 \begin{cases}
  e^{-\alpha_*x^2/2},& |x|\le1/2,\\
  1-e^{-\alpha_*(1-|x|)^2/2},& 1/2<|x|\le1,\\
  0,& |x|>1.
 \end{cases}
\]
It is continuous, and for \(0\le x\le1\), \(f_*(x)+f_*(x-1)=1\), so it is a probability density with uniform residue. On the central interval the curvature of \(-\log f_*\) is exactly \(\alpha_*\). In a tail let \(y=1-|x|\in(0,1/2)\) and \(u=\alpha_*y^2/2\in(0,\log2)\); its curvature there is
\[
 \alpha_*\frac{1+(2u-1)e^u}{(e^u-1)^2}\ge\alpha_*.
\]
The inequality reduces to \(e^u\le1+2u\), since \(e^u\) has derivative at most two over this interval. The one-sided first derivatives at \(|x|=1/2\) match: both have absolute value \(\alpha_*/4\). Thus the convex residual potential is valid across the seams and outside the support. Convolution with Gaussians gives smooth positive uniform lifts with (3) arbitrarily close to \(\alpha_*\).

In the continuous class, equality in (2) forces \(f(0)=1\) and \(f(\pm j)=0\) for integer \(j\ge1\); in particular the support is contained in \([-1,1]\). The half-fiber has only two possible nonzero terms; (1) and their sum force \(f(\pm1/2)=1/2\). The log-concave \(g=f e^{\alpha_*x^2/2}\) reaches its maximum 1 at both endpoints of the central interval, so \(g=1\) throughout that interval. The modular identity determines the other two pieces, giving \(f=f_*\).

There is quantitative stability as well. For continuous \(f\) with mode at zero and \(0\le\epsilon=\alpha_*-\alpha\le1\),
\[
 \|f-f_*\|_\infty\le (17/8)\epsilon,\qquad
 \|f-f_*\|_1\le5\epsilon .
 \tag{4}
\]
Indeed (2) gives \(1-f(0)\le2(1-e^{-\epsilon/8})\le\epsilon/4\). The tails of the half-integer fiber, excluding \(\pm1/2\), sum to at most \(\epsilon/4\) by (1). Also each half-site has mass at most \(e^{-\alpha/8}\le1/2+\epsilon/14\), using \(e^{\epsilon/8}\le(1-\epsilon/8)^{-1}\). Thus each has mass at least \(1/2-9\epsilon/28\), and \(g(\pm1/2)\ge1-\epsilon\), since
\((1-9\epsilon/14)e^{-\epsilon/8}\ge1-\epsilon\). Log-concavity and \(g(0)\le1\) give \(1-\epsilon\le g(x)\le1\) on the central interval. Replacing \(\alpha\) by \(\alpha_*\) in its Gaussian factor costs at most \(\epsilon/8\), yielding the central difference \(\le9\epsilon/8\).

For \(|x|\ge1\), the same monotonicity on rays and \(f(\pm1)\le\epsilon/4\) give \(f(x)\le(\epsilon/4)e^{-\alpha(|x|-1)}\). In the periodization for \(1/2\le x\le1\), all sites except \(x,x-1\) have absolute value at least 1. Their combined mass is at most \((\epsilon/2)/(1-e^{-\alpha})\le\epsilon\), because each one-sided sequence has unit spacing and \(\alpha>4\). Thus the outer difference is at most \(17\epsilon/8\), and the identical reasoning holds after reflection. The total mass outside \([-1,1]\) is at most \(\epsilon/(2\alpha)\), giving (4).

For uniqueness among arbitrary densities at \(\alpha_*\), convolve with a sequence of Gaussians with \(\sigma\downarrow0\), and apply (4) with deficit \(\alpha_*-\alpha_\sigma\to0\) after translating each smooth mode. The original convolutions converge to \(f\) in \(L^1\), so the translates of \(f_*\) converging to them have bounded translation parameters (otherwise their mass escapes every compact interval). Taking a convergent subsequence of the centers shows \(f\) is a translate of \(f_*\) almost everywhere. This also handles nonsmooth representatives at equality.

## 3. General dual obstruction and exact rectangular case

Let \(L\subset\mathbb R^n\) be full rank and let \(v\in L^*\setminus\{0\}\). The map \(x+L\mapsto\langle v,x\rangle+\mathbb Z\) is a surjective torus homomorphism, so the real variable \(Y=\langle v,X\rangle\) from a uniform lift is uniform modulo \(\mathbb Z\). The orthogonal marginal along \(v/\|v\|\) preserves \(\alpha\)-strong log-concavity by Prékopa: factor out the fixed Gaussian in the retained coordinate and integrate the log-concave residual against the Gaussian in the other coordinates. Scaling by \(\|v\|\) gives curvature \(\alpha/\|v\|^2\) for \(Y\). Therefore
\[
 \alpha\le 8\log2\,\lambda_1(L^*)^2.
\]
For full-support smooth lifts the inequality is strict, by applying (2) to the continuous positive marginal along a shortest dual vector. This improves the shortest-vector part of the converse estimate \(2\pi\,\lambda_1(L^*)^2\) from the general determinant-based criterion; it does not replace that criterion for higher-rank dual sublattices.

For \(L=\bigoplus_i a_i\mathbb Z\) along orthogonal axes, take the product of the scaled one-dimensional extremizers \(a_i^{-1}f_*(x_i/a_i)\). It is uniform modulo this lattice and has curvature \(\alpha_*/(\max_i a_i)^2\), matching the upper bound. The Gaussian convolutions of the product give the same supremum in the smooth positive class. In particular the exact dimension-free supremum on \(\mathbb R^n/\mathbb Z^n\) is \(8\log2\).

## Verification and scope

The replay makes 38,025 exact completing-square checks and 4,101 numerical checks of periodization, the tail curvature formula, and the Gaussian-smoothed profile. The extremal proof is analytic and does not depend on numerical optimization. The result is about densities and curvature on flat tori; it does not give a procedure for solving a lattice learning problem or any conclusion about a particular cryptographic scheme.
