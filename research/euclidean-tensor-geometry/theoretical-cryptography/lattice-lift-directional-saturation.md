# Saturation of the sharp rank-one obstruction for lattice lifts

Let \(\mathcal A(L)\) be the supremal strong log-concavity parameter of a smooth strictly positive probability density that reduces to Haar uniform measure on \(\mathbb R^n/L\). Strong log-concavity with parameter \(\alpha>0\) means \(f(x)e^{\alpha\|x\|^2/2}\) is log-concave. Allowing densities with zeros does not change the supremum, since convolution with small Gaussian variance \(\sigma^2\) preserves uniform reduction and changes the parameter to at least \(\alpha/(1+\alpha\sigma^2)\).

The [sharp scalar lift](strongly-logconcave-lattice-lift-sharp.md) gives \(A=8\log 2\), \(\mathcal A(\mathbb Z)=A\), and the upper bound \(\mathcal A(L)\le A\lambda_1(L^*)^2\). **We determine exactly when the directional bound can be saturated:**
\[
 \boxed{\quad
 \mathcal A(L)=A\|u\|^2
 \quad\Longleftrightarrow\quad
 \mathcal A(L\cap u^\perp)\ge A\|u\|^2,\qquad u\in L^*\text{ primitive}.
 \quad} \tag{1}
\]
The perpendicular lattice is considered in its own Euclidean span. The criterion includes sheared lattices, not just orthogonal products. In dimension two it becomes an exact condition in terms of covolume and the shortest dual vector. In particular the hexagonal lattice fails to saturate the directional bound, by a strictly positive and explicit gap. This note does not determine its actual optimum.

## 1. Skew coordinates and the product lower bound

Fix primitive \(u\in L^*\), write \(\ell=\|u\|\), and let \(H=u^\perp,\ \Gamma=L\cap H\). Primitivity means that \(\langle u,L\rangle=\mathbb Z\): if its image were \(k\mathbb Z\) with \(k>1\), then \(u/k\in L^*\). Select \(b\in L\) with \(\langle u,b\rangle=1\). Write \(x=t u/\ell^2+y\), \(t=\langle u,x\rangle,\ y\in H\), and \(b=u/\ell^2+y_0\). On reducing modulo \(L\), unique coordinates modulo null boundaries are
\[
 \left(t-k,\ y-k y_0+\Gamma\right),\qquad
 k=\lfloor t+1/2\rfloor.
 \tag{2}
\]
Indeed subtract \(kb\) and then reduce the transverse coordinate modulo \(\Gamma\). An interval of length one in \(t\) times a fundamental cell of \(\Gamma\) is a fundamental domain, with constant Jacobian \(1/\ell\). Therefore Haar measure is exactly the product of uniform measure on \([-1/2,1/2)\) and Haar on \(H/\Gamma\) in (2).

Taking independent lifts in the orthogonal normal and transverse coordinates gives
\[
 \mathcal A(L)\ge\min\{A\ell^2,\mathcal A(\Gamma)\}.
 \tag{3}
\]
The normal lift, on the unit coordinate \(t/\ell\), has supremum \(A\ell^2\). Independence means that subtracting the shear \(k y_0\) from the already uniform transverse residue does not change Haar measure, even conditionally on the whole \(t\). Curvatures of a product in Euclidean orthogonal coordinates take the minimum. Conversely projection of any lift to \(t=\langle u,X\rangle\) has curvature at least \(\alpha/\ell^2\), is uniform modulo \(\mathbb Z\), and hence \(\alpha\le A\ell^2\). This projection argument uses [Prékopa's marginal theorem](https://acta.bibl.u-szeged.hu/14411/) after taking out the Gaussian factor. It proves the reverse inequality needed for the sufficient direction of (1).

## 2. Near extremizers force a transverse lift

Suppose \(\mathcal A(L)=A\ell^2\). Take smooth positive uniform lifts with curvature parameters \(\alpha_j\to A\ell^2\) from below. The marginal densities of \(t_j=\langle u,X_j\rangle\) have curvature at least \(A-\epsilon_j\), where \(\epsilon_j=A-\alpha_j/\ell^2\to0\). Translating each \(X_j\) in its normal coordinate centers the mode of that marginal at zero and preserves uniform reduction. The scalar stability inequality gives
\[
 \|f_{t_j}-f_*\|_1\le5\epsilon_j
\]
for small enough \(\epsilon_j\), where \(f_*\) is the compactly supported optimum on \([-1,1]\). Its two outer ends vanish quadratically: \(f_*(1-s)=f_*(-1+s)=1-e^{-As^2/2}\le3s^2\) for \(0\le s\le1/2\).

For small positive \(\delta\), let \(C_\delta=\{|t_j|\le\delta\}\) and \(B_\delta=\{\operatorname{dist}(t_j,\mathbb Z)\le\delta\}\). The latter has probability \(2\delta\) by exact uniform reduction. The mass that wraps from a different layer satisfies
\[
 \Pr(B_\delta\setminus C_\delta)\le2\delta^3+5\epsilon_j,\quad 0<\delta<1/2.
 \tag{4}
\]
For \(f_*\) only the two intervals adjacent to \(t=\pm1\) contribute, each with integral at most \(\delta^3\). The \(L^1\) difference gives the remaining error. Conditional on \(B_\delta\), the transverse residue in (2) is uniform. Conditional on \(C_\delta\), the shear index is zero, so this residue is the projection of \(y_j\) itself modulo \(\Gamma\). The two conditional residues differ in total variation by at most
\[
 \frac{2\delta^3+5\epsilon_j}{2\delta}.
 \tag{5}
\]
Indeed one law is a mixture of the component on \(C_\delta\) and the wrapped layers, with outlier weight exactly \(\Pr(B_\delta\setminus C_\delta)/(2\delta)\).

Set \(\delta_j=\epsilon_j^{1/3}\); all sufficiently large \(j\) lie in the indicated range. The law of \(y_j\) conditional on \(C_{\delta_j}\) has curvature at least \(\alpha_j\): restrict the joint density to a convex slab (multiplication by a log-concave indicator) and project orthogonally by Prékopa. Its residue approaches Haar by (5). Here is a compactness step that avoids asserting positivity of a limiting density. Convolve these transverse laws with arbitrarily small Gaussians, tending to zero with \(j\), so they are smooth positive, with parameters still tending to \(A\ell^2\); the residue errors only decrease under convolution on the torus. Translate each transverse mode to zero. These translations preserve the errors because Haar is invariant. The resulting laws are tight, since in dimension \(d=\dim H\), any smooth positive \(\beta\)-strongly log-concave density with mode zero has \(\mathbb E\|Y\|^2\le d/\beta\). To see this elementary bound, use polar coordinates and \(f=e^{-\beta\|x\|^2/2}h(x)\). Along each ray, \(h\) is nonincreasing. Multiplying the standard Gaussian radial measure by this decreasing factor cannot increase its mean squared radius (use the two-copy covariance identity for an increasing and a decreasing function). The bound holds for almost every direction, and hence after averaging.

Take a weak limit of a subsequence of these tight laws. Its projection to \(H/\Gamma\) is Haar by continuity of the quotient. For any fixed \(\sigma>0\) convolve the weak limit with a Gaussian on \(H\) of variance \(\sigma^2\); the densities of the corresponding convolutions of the approximating laws converge pointwise, since the Gaussian kernel at each point is bounded continuous. The strong log-concavity inequalities pass to the limit pointwise after removing the quadratic factor. Hence this smooth positive limiting convolution has uniform residue and curvature at least
\[
 \frac{A\ell^2}{1+A\ell^2\sigma^2}.
\]
Letting \(\sigma\downarrow0\) proves \(\mathcal A(\Gamma)\ge A\ell^2\), the necessary part of (1).

## 3. A quantitative transverse obstruction

One can get a dimension-independent explicit gap from any too-short transverse dual vector \(w\in\Gamma^*\setminus\{0\}\) with \(\|w\|<\ell\). Let
\[
 r=\frac{\ell^2}{\|w\|^2}>1,\qquad
 \kappa(r)=\min\!\left\{\frac1{512},
  \left(\frac{A(r-1)}
   {r+(64+4A^2r^2)(7/2)^{2/3}}\right)^{9/4}\right\}>0.
\]
Then
\[
 \mathcal A(L)\le \ell^2(A-\kappa(r)). \tag{6}
\]
To check this, we first record a scalar approximate-uniformity bound. If a \(\beta\)-strongly log-concave real law has circular residue at total variation distance \(\tau\le1/8\) from Haar and \(\beta\le B\), then
\[
 \beta\le A+(64+4B^2)\tau^{2/3}. \tag{7}
\]
For \(\tau=0\) this is the sharp scalar bound. Otherwise convolve the law with a Gaussian of standard deviation \(s=(8\tau)^{1/3}\le1\). The wrapped Gaussian has supremum at most \(2/s\): its Fourier coefficients are nonnegative, so the maximum is at zero, where a decreasing integral bound on the two tails gives at most \(1+1/(s\sqrt{2\pi})\le2/s\). Thus the smoothed residue density differs uniformly from one by at most \(4\tau/s=\eta=2\tau^{2/3}\le1/2\); the factor two between signed variation mass and total variation distance is included here. Its curvature is at least \(\beta_s=\beta/(1+\beta s^2)\). Comparing the integer and half-integer sums around its mode, exactly as in the two-fiber scalar proof, gives
\[
 1-\eta\le 2(1+\eta)e^{-\beta_s/8};
 \qquad
 \beta_s\le A+8\log((1+\eta)/(1-\eta))\le A+32\eta.
\]
The loss \(\beta-\beta_s\) is at most \(B^2s^2=4B^2\tau^{2/3}\), proving (7).

Now for a lift on \(L\) write \(\epsilon=A-\alpha/\ell^2>0\). If \(\epsilon>1/512\) then (6) is immediate. Otherwise condition as in §2 with \(\delta=\epsilon^{1/3}\le1/8\), and project \(y\) further to \(\langle w,y\rangle\). Its circular residue error is at most \((7/2)\epsilon^{2/3}<1/8\) by (5), since projection onto \(\mathbb R/\mathbb Z\) maps transverse Haar to Haar. The scalar conditional curvature is at least \(\beta=\alpha/\|w\|^2=r(A-\epsilon)\le Ar\). Substitution into (7) gives
\(A(r-1)\le r\epsilon+(64+4A^2r^2)(7/2)^{2/3}\epsilon^{4/9}\).
Since \(0<\epsilon\le1\), this implies (6).

## 4. Planar criterion and nonorthogonal shortest vectors

For dimension two, take \(u\) shortest in \(L^*\); it is primitive. If \(\lambda=\|u\|\) and \(a\) is the spacing of the line lattice \(\Gamma\), the fundamental-domain volume in (2) gives \(a=\lambda\,\mathrm{covol}(L)\). By the scalar result, \(\mathcal A(\Gamma)=A/a^2\), so (1) becomes
\[
 \mathcal A(L)=A\lambda_1(L^*)^2
 \quad\Longleftrightarrow\quad
 \mathrm{covol}(L)\lambda_1(L^*)^2\le1.
\]
In particular it is not a statement that all nonorthogonal lattice shapes fail: some sheared shapes meet this condition.

In any dimension, if \(L^*\) has two independent nonorthogonal shortest vectors \(u,v\), the projection \(w\) of \(v\) to \(H=u^\perp\) is nonzero and belongs to \(\Gamma^*\), since it has integral pairing with every vector of \(\Gamma\). It has strictly smaller norm than \(u\). Thus (6) strictly separates such a lattice from the rank-one bound. For a hexagonal dual normalized to shortest length one, take shortest vectors meeting at \(60^\circ\), giving \(r=4/3\). The formula yields a positive gap of about \(1.85\cdot10^{-6}\) below \(A\), without determining the exact optimum in the hexagonal case.

[Letwin–Reis–Rothvoss](https://arxiv.org/abs/2610.29238) use a construction that can split off a subspace in their universal lower bound. The new part here is **necessity of a transverse lift at directional saturation**, obtained despite possible compact support or lack of exact saturation by any smooth lift. The verification script checks 398,413 exact modular-coordinate statements and 560 scalar consistency inequalities; the proofs of compactness and of the quantitative gap are analytic. No conclusion about a specific cryptographic scheme is claimed.
