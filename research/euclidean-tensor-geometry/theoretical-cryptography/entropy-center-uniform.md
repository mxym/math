# Centered entropy minimization on nonorthogonal lattice Gaussians

A discrete Gaussian on a coset of a fixed lattice is not obtained by simply translating its centered distribution. Its entropy can change. The zero coset minimizes every positive-order Rényi entropy in the following non-product regimes:

* **Planar lattices with** \(\lambda_1(L)^2/\det L\ge 5/(2\pi)\), including square and triangular shapes and an explicit region of nonorthogonal shapes.
* **All lattices in an open neighborhood** of any orthogonal direct sum of rank-one lattices and of planar lattices satisfying that bound. Perturbations in this neighborhood may mix all blocks. The neighborhood depends on the starting lattice, but is common to every width, every shift and every positive order.
* For any fixed lattice, two explicit precision intervals give **uniform-in-shift** strict Shannon comparison. On a width interval where the stated Shannon condition holds throughout, comparison extends to every Rényi order whose two evaluation precisions lie in that interval.

The general all-width comparison on arbitrary lattices is not established. This note concerns unwrapped probability laws on lattice cosets. It does not claim a property of learning samples, a cryptographic hardness result, or a sampling algorithm.

## 1. Formulation and literature

For \(L\subset\mathbb R^d\) full rank, \(z\in\mathbb R^d/L\), and precision \(t>0\), write
\[
 Z_t(z)=\sum_{x\in L+z}e^{-t\|x\|^2},\quad
 R_t(z)=\frac{Z_t(z)}{Z_t(0)},\quad
 g_t(z)=-\log R_t(z),\quad
 E_L(t)=\frac{\sum_{x\in L}\|x\|^2e^{-t\|x\|^2}}{Z_t(0)} .
\]
The width convention \(e^{-\pi\|x\|^2/s^2}\) corresponds to \(t=\pi/s^2\). Write \(H_\alpha(t,z)\) for the entropy of the normalized mass, with natural logarithms. For finite positive orders the exact differences are
\[
\begin{aligned}
 H_1(t,z)-H_1(t,0)&=t\partial_t g_t(z)-g_t(z),\\
 H_\alpha(t,z)-H_\alpha(t,0)
   &=\frac{g_{\alpha t}(z)-\alpha g_t(z)}{\alpha-1}
     \quad(\alpha\ne1). \tag{1}
\end{aligned}
\]
Thus pointwise strict positivity of the first line on an entire interval says exactly that \(g_t(z)/t\) strictly increases there, which gives the second comparison when \(\min(t,\alpha t)\) and \(\max(t,\alpha t)\) belong to that interval. In particular a Shannon sign for all \(t\) is enough for all finite positive orders. Min-entropy is dealt with directly below.

[Regev–Stephens-Davidowitz, Propositions 4.1–4.2](https://arxiv.org/abs/1502.04796) show monotonicity of \(R_t(z)\) as width changes; here the question involves \(-\log R_t(z)/t\), an additional normalization. [Agostini–Améndola](https://arxiv.org/abs/1801.02373) develop the entropy and cumulant formulas for lattice Gaussians. The [earlier shift-entropy note](lattice-gaussian-shift-entropy.md) gives all orders for orthogonal products, integer and reciprocal-integer orders for arbitrary lattices, and endpoint asymptotics for a *fixed* shift. We seek uniform endpoint inequalities and all widths and orders on genuinely nonorthogonal open sets. The proof below is independent of the earlier rank-one Jacobi-product argument.

## 2. Two uniform, one-precision tests

Set \(\ell=\lambda_1(L)\), \(\ell^*=\lambda_1(L^*)\), and \(\beta=\pi^2/t\). For any nonzero coset, the Shannon gap is strictly positive if either
\[
 \beta\bigl((\ell^*)^2-E_{L^*}(\beta)\bigr)\ \ge\ 1, \tag{W}
\]
or
\[
 \frac{2t\ell^2}{e^{t\ell^2}-1}+t E_L(t)\ \le\ 1. \tag{N}
\]
Both tests are independent of the shift \(z\). A simpler sufficient condition for (W) is \(\beta(\ell^*)^2\ge 1+d/2\); a dimension-only sufficient condition for (N) is \(t\ell^2\ge 10(d+1)\). The simpler bounds are not asserted sharp.

**Wide-side proof.** Poisson summation gives
\[
 R_t(z)=1-w,\quad
 w=\frac{D_\beta(z)}{A_\beta},\quad
 A_\beta=\sum_{u\in L^*}e^{-\beta\|u\|^2},\quad
 D_\beta(z)=\sum_{u\in L^*}e^{-\beta\|u\|^2}(1-\cos(2\pi u\cdot z)).
\]
On a nonzero coset \(0<w<1\): the numerator has a positive term since \(L^{**}=L\), and \(R_t(z)>0\). The \(D\)-weighted energy average \(E_D\) is at least \((\ell^*)^2\). Differentiating with \(\beta=\pi^2/t\) gives \(t\partial_t w=\beta(E_D-E_{L^*}(\beta))w\). With \(c=\beta((\ell^*)^2-E_{L^*}(\beta))\),
\[
 H_1(t,z)-H_1(t,0)
 \ge c \frac{w}{1-w}+\log(1-w). \tag{2}
\]
This is strictly positive for \(c\ge1\), since \(-\log(1-w)<w/(1-w)\). Moreover if \(c>1\) the bound is at least \((c-1)w/(1-w)\). At \(z=0\), \(w\) has a strictly positive definite quadratic term because the dual lattice spans every direction. Therefore a strict margin in (W) gives a positive definite shift Hessian of the Shannon gap at zero.

Differentiating the centered Poisson identity also gives
\[
 t E_L(t)+\beta E_{L^*}(\beta)=d/2. \tag{3}
\]
Both terms are strictly positive, so \(\beta(\ell^*)^2\ge 1+d/2\) guarantees a strict margin in (W).

**Narrow-side proof.** Choose a representative \(v\in L+z\) of minimum Euclidean norm; this does not depend on \(t\). Then \(2|\lambda\cdot v|\le\|\lambda\|^2\) for every \(\lambda\in L\), by comparison to \(v+\lambda\) and \(v-\lambda\). Pair \(\lambda\) and \(-\lambda\) to write
\[
 e^{t\|v\|^2} Z_t(z)=Z_t(0)+T_t(v),\qquad
 T_t(v)=\sum_{\lambda\in L}e^{-t\|\lambda\|^2}\bigl(\cosh(2t\lambda\cdot v)-1\bigr).
\]
Set \(u=T_t(v)/Z_t(0)>0\) for \(z\notin L\). For a nonzero summand, put \(x=t\|\lambda\|^2\) and \(y=2t|\lambda\cdot v|\le x\). Its logarithmic derivative times \(t\) is
\[
 -x+y\coth(y/2)\le -x+x\coth(x/2)=\frac{2x}{e^x-1}
 \le\frac{2t\ell^2}{e^{t\ell^2}-1}.
\]
The first inequality uses monotonicity of \(y\coth(y/2)\), from \(\sinh(y)>y\); the last uses monotonic decrease of \(x/(e^x-1)\). Summing and differentiating the denominator yield \(t u'/u\le b\), where \(b\) is the left side of (N). As \(g_t(z)=t\|v\|^2-\log(1+u)\), one obtains
\[
 H_1(t,z)-H_1(t,0)\ \ge\ \log(1+u)-b\frac{u}{1+u}. \tag{4}
\]
This is strictly positive for \(b\le1\). If \(b<1\) the gap is at least \((1-b)u/(1+u)\), giving a positive definite shift Hessian at zero: near zero \(v=z\), and the quadratic term of \(T_t\) is \(2t^2\sum_\lambda e^{-t\|\lambda\|^2}(\lambda\cdot z)^2\). All derivatives are justified by locally normally convergent Gaussian sums, including near a nearest-point tie, where the chosen \(v\) remains fixed for differentiation in \(t\).

The min-entropy gap at any \(t>0\) is exactly \(\log(1+u)>0\): the largest point mass in the shifted coset is \(e^{-t\|v\|^2}/Z_t(z)\). This direct argument does not require either test (compare the min-entropy bounds under smoothing in [Gentry–Peikert–Vaikuntanathan, Lemma 2.10](https://people.csail.mit.edu/cpeikert/pubs/trap_lattice.pdf)).

For the dimension-only narrow threshold, set \(x=t\ell^2\). Disjoint balls of radius \(\ell/2\) show that a ball of radius \((k+1)\ell\) contains at most \((2k+3)^d\) lattice vectors. The shells \(k\ell\le\|\lambda\|<(k+1)\ell\), \(k\ge1\), therefore give
\[
 t E_L(t)\le x\sum_{k\ge1}(k+1)^2(2k+3)^d e^{-x k^2}.
\]
If \(x\ge10(d+1)\), use \(2k+3\le5^k\), \(\log 5<2\), and \((k+1)^2\le4^k\) to bound the last quantity by \(x\,4e^{-4x/5}/(1-4e^{-4x/5})<1/4\). Indeed \(x\ge20\), the numerator is decreasing there, and \(e^{16}>2^{16}\) gives the claimed rational bound. The first term in (N) is at most \(40/(2^{20}-1)<1/4\). Both simplified precision intervals thus give strict signs and the corresponding Hessian margin.

## 3. All widths on an explicit planar region

For rank two, normalize a shortest lattice vector to length one and complete it to a reduced basis. A shortest vector is primitive; subtracting a nearest integer multiple of it from the second basis vector makes the Gram form
\[
 Q(m,n)=m^2+v n^2+2c mn,\qquad v\ge1,\quad |c|\le\tfrac12 .
\]
All such forms dominate \(m^2+n^2-|mn|\ge1\) on nonzero integral vectors. We show
\[
 x E_L(x)<\frac23\qquad(x\ge x_0=25/8) \tag{5}
\]
in the normalization \(\ell=1\).

First let \(Q_H=m^2+n^2+mn\) be the hexagonal form, of minimum one. It has six vectors of norm squared one, no vectors of norm squared two, and six of norm squared three (these counts follow by listing \(-2\le m,n\le2\), using \(Q_H\ge\tfrac34\max(m^2,n^2)\)). For any integer \(k\ge4\) the number of vectors with \(Q_H=k\) is at most \((2\sqrt k+1)^2\le9k\) by disjoint radius-\(1/2\) disks. With \(q=e^{-x}\), and using \(1+6q\) for a lower bound on its partition sum, obtain
\[
 x E_H(x)\le \frac{6x}{e^x+6}+18x q^3+
          \frac{144x q^4}{1-(25/16)q}. \tag{6}
\]
For the last term sum \(9x\sum_{k\ge4} k^2 q^k\) using the ratio bound \(25q/16\). The first term of (6) decreases for \(x\ge x_0\), as \(e^x(x-1)>6\). The tail estimate can also be maximized at \(x_0\), termwise using that \(x e^{-kx}\) decreases there for \(k\ge3\). The elementary exponential estimate \(e^{25/8}>45/2\) follows from the positive Taylor polynomial through order eight. Thus (6) is bounded above by the rational number
\[
 \frac{25}{38}
   +18\frac{25}{8}\left(\frac{2}{45}\right)^3
   +\frac{144(25/8)(2/45)^4}{1-(25/16)(2/45)}
   \ <\ \frac23 . \tag{7}
\]

To compare every reduced form to the hexagonal one at this precision, use \(\Psi(u)=(u-2/3)e^{-u}\), which is decreasing and convex on \(u\ge x_0\). The sum \(\sum_{(m,n)\ne(0,0)}\Psi(xQ(m,n))\) increases when \(v\) is reduced to one. With \(v=1\), pair the two signs of \(mn\); each pair is of the form \(\Psi(s+r)+\Psi(s-r)\) with \(r\ge0\), and increases as \(|c|\) increases to \(1/2\) by convexity. The terms with \(mn=0\) do not depend on \(c\). All arguments stay in \([x_0,\infty)\) in these comparisons. The resulting upper bound is the hexagonal sum, which is less than \(2/3\) by (7), since
\[
 \sum_{x\in L_H,\ x\ne0}\Psi(t\|x\|^2)-2/3
   =Z_t(0)\bigl(tE_H(t)-2/3\bigr).
\]
The same identity for the given lattice proves (5). For general \(\ell\), this says \(tE_L(t)<2/3\) whenever \(x=t\ell^2\ge25/8\).

At \(x\ge25/8\), \(2x/(e^x-1)\le (25/4)/(45/2-1)=25/86\), and \(25/86+2/3<1\). Thus (N) holds strictly on \(t\ell^2\ge25/8\). The dimension-based version of (W) holds strictly on \(\beta(\ell^*)^2\ge2\). In rank two the dual lattice is a quarter-turn of \(L\) scaled by \(1/\det L\), so the product of these two threshold coordinates is \(\pi^2(\ell^2/\det L)^2\). If \(\ell^2/\det L\ge5/(2\pi)\), the product is at least \((25/8)2\), hence at least one condition is satisfied at every precision. Equations (1)–(4) give strict centered optimality at every positive order and positive definite shift Hessian for Shannon at every precision. This allows equality in the shape bound. A strictly nonorthogonal example is \(m^2+n^2+mn/2\), with two shortest directions having nonzero inner product and \(\det L=\sqrt{15}/4\). Lattices outside this shape region are not ruled out and the shape constant is not an optimal threshold.

## 4. All orders uniformly near products

First a short standalone rank-one comparison follows from the same two tests. Normalize \(L=\mathbb Z\). For \(x\ge3\),
\[
 x E_{\mathbb Z}(x)\ \le\ 2x\sum_{k\ge1}k^2 e^{-x k^2}
 \ \le\ 6\sum_{k\ge1} k^2 (1/20)^k
 =6\,\frac{(1/20)(1+1/20)}{(1-1/20)^3}.
\]
Here \(e^3>20\) by the Taylor polynomial through order eight, and \(x e^{-x k^2}\) is decreasing for \(x\ge3\). The bound plus \(6/19\) is less than one, proving strict (N) on \(t\ge3\). Strict (W) holds if \(\beta\ge3\), covering all \(t\le3\) since \(\pi>3\). Rescaling covers any rank-one lattice. These tests also prove the positive definite Shannon shift Hessian at zero at every width, by (2) and (4).

For a direct orthogonal sum, the law factors and Shannon entropies and their shift Hessians add on the appropriate coordinates. At any fixed precision the strict gap holds on every nonzero coset and the shift Hessian at zero is positive definite for any starting lattice \(L_0\) as in the opening statement.

Fix a basis of \(L_0\) and let \(G_0\) be its positive definite Gram matrix. Parametrize nearby lattices by Gram matrices \(G\) in the same integer coordinates, with fractional shift \(z\) in \([-1/2,1/2]^d\) modulo \(\mathbb Z^d\). On a sufficiently small closed neighborhood of \(G_0\), both \(\lambda_1(L_G)\) and \(\lambda_1(L_G^*)\) are uniformly bounded below by a positive constant, by uniform positive definiteness of \(G\) and \(G^{-1}\). The simplified tests in §2 give common positive precision thresholds \(t_{\rm low}<t_{\rm high}\) with the strict comparison for every nonzero shift outside this interval. It remains to take \(t\in[t_{\rm low},t_{\rm high}]\).

In fixed coordinates the Shannon gap is jointly continuous in \(G,t,z\), and its derivatives of every order in \(z\) are continuous on this compact family, by Gaussian normal convergence. The Hessian at \(z=0\) for \(G_0\) has a uniformly positive smallest eigenvalue on the compact precision interval. The gradient vanishes at zero for every \(G,t\) by reflection, and the gap there is zero. Shrink the Gram neighborhood and fix a radius \(\delta>0\) so the Hessian remains positive definite on \(\|z\|\le\delta\) for all these \(t\). Taylor's integral formula now gives strict positivity for \(0<\|z\|\le\delta\). Outside that ball, the shift domain in the centered cube is compact and contains no nonzero representative of the zero coset. The positive \(G_0\) gap on this remaining compact set has a positive minimum, which persists on shrinking the same Gram neighborhood again. This single open neighborhood is independent of \(t,z\) and gives every positive finite Rényi order by (1). The strict min-entropy claim follows as above. The argument does not give a dimension-free size for the neighborhood.

**Replay.** Run `python3 verify-entropy-center-uniform.py` for the exact arithmetic bounds, hexagonal shell counts, and a finite rational check of the shape-region normalization. The proof does not use numerical searches or any practical parameters.
