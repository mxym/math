# Sharp asymptotics for two-sided noise smudging under a Euclidean variance budget

A standalone smudging step adds independent noise to hide an unknown bounded shift. We study the best possible worst-shift total variation before wrapping, with a Euclidean shift bound and a total second-moment budget. For arbitrary distributions, we prove a finite-dimensional sandwich, identify the exact high-dimensional limit including the small-budget regime, determine its first finite-dimensional correction, and give a sharp fixed-dimension small-shift limit with rigidity. These results concern a statistical comparison only, not any complete protocol, modulus or implementation.

Write \(B_d(R)\) for the centered Euclidean ball of radius \(R\) in \(\mathbb R^d\), and \(V_d=|B_d(1)|\), with \(V_0=1\). For a law \(\mu\) let \(\mu+z\) denote its translation. Fix \(h>0\) and set
\[
 D_d(u)=\inf_{\mu:\,\int\|x\|^2\,d\mu(x)\le du}
       \ \sup_{\|z\|\le h}\|\mu-(\mu+z)\|_{\rm TV},\qquad u\ge0. \tag{1}
\]
Thus \(u\) is second moment per dimension, not necessarily variance of each coordinate. No absolute continuity, product structure, monotonicity or Gaussianity is required.

## 1. A finite-dimensional sandwich on all budgets

For an integer \(n\ge3\), let \(U^{(n)}\) be uniform on the unit sphere in \(\mathbb R^n\), and define
\[
 G_n(v)=\Pr\!\left[\,|\sqrt{nv}\,U^{(n)}_1|\le h/2\,\right],\qquad v\ge0.
\]
In particular \(G_n(0)=1\). Let \(G_n^{\rm cvx}\) denote the greatest convex function below \(G_n\) on \([0,\infty)\). The following sandwich holds for every \(d\ge3\) and \(u\ge0\):
\[
                 G_d^{\rm cvx}(u)\ \le\ D_d(u)\
                       \le\ G_{d+2}^{\rm cvx}(u).             \tag{2}
\]
The upper bound is attained *within the class of mixtures of centered uniform balls and the atom at zero*. It uses either just one ball or one ball mixed with the atom at zero.

**Lower bound.** Orthogonal averaging of a law preserves its second moment and cannot increase its maximal TV in (1). Indeed, for any fixed \(z\), convexity in the pair of distributions and the change of variables \(x\mapsto Rx\) bound the averaged distance by the original supremum; integrate over orthogonal \(R\). A spherically invariant law is a law of \(\sqrt{dV}\,U^{(d)}\) for a nonnegative radial random variable \(V\) independent of the direction, with \(\mathbb E V\le u\). Test the shifted pair at \(\{x:x_1\le h/2\}\) with \(z=h e_1\). The probability gap is \(\Pr(-h/2<X_1\le h/2)\). Away from the atom at zero the projected laws have no atoms, so the gap is \(\mathbb E G_d(V)\). Convexity and monotonicity of \(G_d^{\rm cvx}\) imply \(\mathbb E G_d(V)\ge G_d^{\rm cvx}(u)\). Monotonicity also follows from the explicit envelope below.

**Upper bound.** Uniform \(X\) on \(B_d(R)\) has second moment \(dR^2/(d+2)\). Its first coordinate divided by \(R\) has the same law as \(U^{(d+2)}_1\), since the ball's cross-section density is proportional to \((1-y^2)^{(d-1)/2}\) for \(-1<y<1\). For the pair of translated balls, the positive part of the signed difference of their uniform densities lies in the halfspace closer to zero, \(\{x:x_1\le \|z\|/2\}\) after orienting \(z\) along \(e_1\). This halfspace maximizes the TV difference for every ball radius simultaneously. The same halfspace maximizes it for the pair of point masses when \(z\ne0\). Therefore the TV of a mixture compared to its own translate is exactly the mixture of the individual TV distances; the maximal shift is of length \(h\) since each slab probability is nondecreasing in length. Taking \(R=\sqrt{(d+2)V}\), with \(R=0\) representing the atom, gives worst-case TV \(\mathbb E G_{d+2}(V)\) under mean budget \(\mathbb E V\le u\). Its minimum is \(G_{d+2}^{\rm cvx}(u)\), realized by choices described next.

**Exact envelope.** Put
\[
 b_n=\frac{h^2}{4n},\qquad
 c_n=\frac{\Gamma(n/2)}{\sqrt\pi\,\Gamma((n-1)/2)}.
\]
For \(v\le b_n\), \(G_n(v)=1\); for \(v>b_n\),
\[
 G_n(v)=2c_n\int_0^{\sqrt{b_n/v}} (1-y^2)^{(n-3)/2}\,dy,\qquad
 G_n'(v)=-c_n\sqrt{b_n}\,v^{-3/2}(1-b_n/v)^{(n-3)/2}.
\]
For \(n>3\), \(G_n\) is strictly concave on \((b_n,h^2/12)\) and strictly convex above \(h^2/12\), by differentiating. For \(n=3\), the concave interval is empty and the one-sided derivative drops at \(b_n=h^2/12\); the function is strictly convex after it. There is a unique \(v_n^*>h^2/12\) with
\[
                     G_n(v_n^*)-v_n^*G_n'(v_n^*)=1.           \tag{3}
\]
In fact the left expression starts at 1 on the plateau, strictly increases on the concave interval (or jumps to \(3/2\) at the \(n=3\) endpoint, using its right derivative), then strictly decreases to 0. It has derivative \(-vG_n''(v)\) off the breakpoint. Thus \((1-G_n(v))/v\) is maximized exactly at \(v_n^*\): its derivative has the sign of \(G_n(v)-vG_n'(v)-1\). This proves that the chord from \((0,1)\) to the tangent point lies below the curve. Joining it to the curve after that point gives a convex minorant. Any convex minorant is below the chord up to the tangent point, by convexity and the two endpoint bounds, and bounded above by the curve thereafter. Consequently
\[
 G_n^{\rm cvx}(v)=
 \begin{cases}
  1+(G_n(v_n^*)-1)v/v_n^*, & 0\le v\le v_n^*,\\
  G_n(v), & v\ge v_n^* .
 \end{cases}                                                 \tag{4}
\]
In particular this function is nonincreasing. For the upper bound in (2) use \(V=u\) when \(u\ge v_{d+2}^*\), and otherwise choose \(V=v_{d+2}^*\) with probability \(u/v_{d+2}^*\) or \(V=0\) with the remaining probability. This proves the asserted restricted-class optimum as well as the general sandwich.

## 2. Sharp high-dimensional expansion

Let \(\Phi,\phi\) be the standard normal CDF and density and, for \(v>0\), put
\[
 \gamma(v)=\frac{h}{2\sqrt v},\qquad
 G(v)=2\Phi(\gamma(v))-1,\qquad
 A(v)=\tfrac12\phi(\gamma(v))(\gamma(v)^3-3\gamma(v)).
\]
Extend \(G(0)=1\). Let \(\gamma_*\in(0,\sqrt3)\) be the unique solution of
\[
       \gamma_*\phi(\gamma_*)=2\Phi(-\gamma_*),
       \qquad v_*=\frac{h^2}{4\gamma_*^2}.
\]
Then the following holds for every fixed \(h>0,u\ge0\) as \(d\to\infty\):
\[
 \boxed{\displaystyle
  D_d(u)=G^{\rm cvx}(u)+\frac{A^{\rm cut}(u)}{d}+O_{h,u}(d^{-2}),
 }\quad
 A^{\rm cut}(u)=
 \begin{cases}
   u A(v_*)/v_* , &0\le u\le v_*,\\
   A(u), &u\ge v_* .
 \end{cases}                                                 \tag{5}
\]
Here \(G^{\rm cvx}\) has the same chord-and-curve form as (4) with \(G,v_*\) instead of \(G_n,v_n^*\). This includes the boundary \(u=v_*\). In particular:
- At \(u\ge v_*\) the Gaussian law has the optimal limiting shift loss, but is larger by the explicit order-\(1/d\) correction for every finite positive fixed \(u\) and large \(d\).
- At \(0<u<v_*\) the optimal limiting loss is strictly below the Gaussian's. The atom-and-ball mixture in (2) already matches (5) to additive \(O_{h,u}(d^{-2})\); the strict improvement over the Gaussian persists in the limit.
The theorem does not identify the exact optimizer over all laws at finite \(d\).

**Proof.** For \(y\) in a fixed bounded interval and \(n\) large, the density of \(\sqrt n\,U^{(n)}_1\) has expansion
\[
 \frac{c_n}{\sqrt n}(1-y^2/n)^{(n-3)/2}
   =\phi(y)\left[1+\frac{-y^4+6y^2-3}{4n}+O(n^{-2})\right].
\]
Indeed, the ratio formula from Stirling gives \(c_n/\sqrt n=(2\pi)^{-1/2}(1-3/(4n)+O(n^{-2}))\); expanding the log of the remaining factor gives \(-y^2/2+(3y^2/2-y^4/4)/n+O(n^{-2})\). The remainders are uniform for bounded \(y\). Integrating from \(-\gamma(v)\) to \(\gamma(v)\), using \((\phi(y)(y^3-3y))'=\phi(y)(-y^4+6y^2-3)\), yields
\[
                G_n(v)=G(v)+A(v)/n+O(n^{-2}).                \tag{6}
\]
Uniformity holds on compact intervals of positive \(v\); using the same endpoint density formula differentiates (6) once with a uniform \(O(n^{-2})\) remainder. More explicitly \(G_n'(v)= -\gamma(v) f_n(\gamma(v))/v\) there, with \(f_n\) the displayed density.

For \(G\), the inflection is again at \(h^2/12\) and its tangent intercept is \(2\Phi(\gamma)-1+\gamma\phi(\gamma)\). As a function of \(\gamma\) this is strictly increasing from 0 to a maximum at \(\sqrt3\), then strictly decreasing to 1. The maximum is strictly above 1 by the strict decrease to its limit. Thus the unique finite intercept-one solution below \(\sqrt3\) exists and is \(\gamma_*\). Equivalently the inflection is found from derivative \((3-\gamma^2)\phi(\gamma)\) of the intercept. As for (4), the line from \((0,1)\) has its maximal slope magnitude at this unique tangent; it is strictly below \(G\) for \(0<v<v_*\). This proves the formula for \(G^{\rm cvx}\).

By (6) and its first derivative, the intercept \(G_n(v)-vG_n'(v)\) differs from \(G(v)-vG'(v)\) by \(O(n^{-1})\) locally uniformly near \(v_*\). The latter has strictly negative derivative there, since \(G''(v_*)>0\); (3)'s uniqueness therefore gives \(v_n^*=v_*+O(n^{-1})\). The function \((G(v)-1)/v\) has zero derivative at \(v_*\), so plugging \(v_n^*\) into (6) and dividing by \(v_n^*\) gives
\[
 \frac{G_n(v_n^*)-1}{v_n^*}
  =\frac{G(v_*)-1}{v_*}+\frac{A(v_*)}{n v_*}+O(n^{-2}).
\]
For \(u<v_*\) fixed, (4) uses this expansion for large \(n\); for \(u>v_*\) it uses (6) directly. At \(u=v_*\) either formula gives the same expansion, so root movement does not affect the first correction. At \(u=0\) the distance is exactly one. The lower and upper curves in (2) now have identical terms of orders 1 and \(1/d\), since \((d+2)^{-1}=d^{-1}+O(d^{-2})\). This proves (5).

For \(u>v_*\) fixed, the attaining ball from (2) is also subgaussian with variance proxy \(u\) in every unit direction. In fact its coordinate's \(2k\)-th moment is
\[
 (2k-1)!!\,u^k\prod_{\ell=0}^{k-1}\frac{d+2}{d+2+2\ell}
       \le (2k-1)!!\,u^k;
\]
odd moments vanish. Sum the moment-generating series (the ball is bounded) to obtain the Gaussian proxy bound. The same conclusion at \(u=v_*\) holds to the precision in (5) by using just the deterministic-radius ball, even if the exact mixture-class optimizer uses a small atom. No equal-proxy statement is made for the smaller-budget mixtures.

## 3. Sharp fixed-dimension small-shift limit and rigidity

In this section display \(h\) as a subscript \(D_{d,h}(u)\) in (1). For every fixed \(d\ge1,u>0\),
\[
 \lim_{h\downarrow0}\frac{D_{d,h}(u)}h
   =\frac{V_{d-1}}{V_d\sqrt{(d+2)u}}.                         \tag{7}
\]
Furthermore, if \(h_j\downarrow0\) and laws \(\mu_j\) with second moment at most \(du\) attain the limiting worst-shift slope in (7), they converge in total variation to the uniform law on \(B_d(\sqrt{(d+2)u})\). Both assertions concern all Borel laws, not only already monotone or smooth densities.

The upper bound follows from the exact slab comparison for a uniform ball: its first-coordinate density is continuous at zero and equals \(V_{d-1}/(RV_d)\) there, with \(R=\sqrt{(d+2)u}\). This also holds for the uniform interval when \(d=1\).

For the lower bound, consider a sequence \(h_j\downarrow0\) with bounded worst-shift slope, allowing a different arbitrary law \(\mu_j\) for each \(h_j\). Pass to a subsequence along which the slopes tend to their liminf \(L<\infty\), and by the uniform second-moment bound to a weak limit \(\mu\). It has second moment at most \(du\). For each unit vector \(e\) and every smooth compactly supported \(\psi\) with \(\|\psi\|_\infty\le1\),
\[
 \left|\int\partial_e\psi\,d\mu\right|
  =\lim_j\left|
      \int\frac{\psi(x+h_j e)-\psi(x)}{h_j}\,d\mu_j(x)\right|
  \le 2L.
\]
The equality uses uniform convergence of difference quotients of the fixed test, followed by weak convergence. The factor 2 uses the convention TV is half the variation norm. Therefore the distributional derivative \(D_e\mu\) is a finite signed measure with variation norm at most \(2L\). In particular \(\mu\) has a nonnegative probability density \(f\) of bounded variation. One way to see this is to convolve \(\mu\) with smooth nonnegative approximate identities; their \(L^1\) norms are 1 and their coordinate derivatives have uniformly bounded \(L^1\) norms by the preceding measure estimates. Local BV compactness gives a subsequential \(L^1_{\rm loc}\) limit, which must be the density of the weak measure limit \(\mu\). This also gives the claimed derivative bounds for \(f\).

Let \(\operatorname{Var}(f)=|Df|(\mathbb R^d)\). Averaging \(|D_e f|(\mathbb R^d)\) over the unit sphere gives \(\kappa_d\operatorname{Var}(f)\), where \(\kappa_d=\mathbb E|U^{(d)}_1|=2V_{d-1}/(dV_d)\) (with the same identity for \(d=1\)). Indeed the polar decomposition \(Df=\nu\,|Df|\) has \(\|\nu\|=1\) almost everywhere and \(|D_e f|=|e\cdot\nu|\,|Df|\). Thus \(2L\ge\kappa_d\operatorname{Var}(f)\).

For \(y>0\) let \(S_y=\{x:f(x)>y\}\), and let \(R_y\) be such that \(|S_y|=V_dR_y^d\). The BV coarea identity and Euclidean isoperimetry give \(\operatorname{Var}(f)\ge\int_0^\infty d\,|S_y|/R_y\,dy\), ignoring levels of zero volume. Layer cake for the moment, and moving each level set to the centered ball of the same volume, give
\[
 du\ \ge\ \int\|x\|^2 f(x)\,dx
       \ \ge\ \frac d{d+2}\int |S_y| R_y^2\,dy.
\]
The moment of a fixed-volume set is minimized at the centered ball because squared radius increases strictly with radius; equality forces the set to agree with the ball up to null sets. The weights \(|S_y|\,dy\) form a probability measure. Jensen for \(x\mapsto x^{-1/2}\) therefore yields
\[
 \operatorname{Var}(f)\ \ge\ d\,\mathbb E[R_y^{-1}]
    \ \ge\ d\,(\mathbb E R_y^2)^{-1/2}
    \ \ge\ \frac d{\sqrt{(d+2)u}} .
\]
This proves (7). If \(L\) equals the displayed optimal slope, all inequalities must be equalities. Strict convexity in Jensen forces almost every positive-volume level to have the same radius; equality in the moment comparison makes those levels centered balls. Their common radius is \(\sqrt{(d+2)u}\), and normalization and layer cake identify the uniform density. Thus every subsequential weak limit of an optimal sequence is this same law.

To strengthen weak convergence to TV, assume the worst-shift slopes along the sequence are at most \(L_0<\infty\). Split any shift \(z\) into \(\lceil\|z\|/h_j\rceil\) steps of norm at most \(h_j\). The triangle inequality gives \(\|\mu_j-(\mu_j+z)\|_{\rm TV}\le L_0(\|z\|+h_j)\). Convolution by a smooth probability kernel supported at radius \(\epsilon\) thus changes \(\mu_j\) in TV by at most \(L_0(\epsilon+h_j)\). At each fixed \(\epsilon>0\), the convolved densities converge pointwise by the weak convergence, and in \(L^1\) by their common unit mass. Finally the limiting uniform-ball density is approximated in \(L^1\) by its own smoothings as \(\epsilon\downarrow0\). The triangle inequality proves the stronger assertion without assuming the approximating laws have densities.

## 4. Prior scope and statistical use

- [Geng–Ding–Guo–Kumar (AISTATS 2019), Theorems 2–3](https://proceedings.mlr.press/v89/geng19a/geng19a.pdf) find the one-dimensional atom-and-uniform optimum under a symmetric decreasing density assumption with an allowed point mass, for general moment costs. The higher-dimensional shape in (2) is an analogous restricted-class optimum. The arbitrary-law lower bound (2), high-dimensional squeeze (5), and unrestricted small-shift slope (7) use different arguments from that one-dimensional result.
- [Wei–Bienstock–Polychroniadou (ICML 2026), Theorem 3.1, Lemma 3.3, Appendix B](https://arxiv.org/pdf/2606.08681) prove leading-order high-dimensional Gaussian optimality at sufficiently high privacy for general hockey-stick divergence. Haar symmetrization, a projection test and a tangent-based Jensen bound are ingredients there. They explicitly leave dimension convergence rates open after Theorem 3.1. At the total-variation endpoint only (zero multiplicative privacy parameter), (5) supplies the finite-dimensional \(1/d\) term with an \(O(d^{-2})\) remainder and the other-budget leading curve. The added upper certificate uses the *exact* \(d\)-ball/\((d+2)\)-sphere coordinate relationship. We do not improve their nonzero-parameter theorem.
- [Cheon–Cho–Kim, *Improved Universal Thresholdizer from Iterative Shamir Secret Sharing*, Lemma 3.1](https://eprint.iacr.org/2023/545.pdf) use bounded uniform noise in a standard statistical noise-flooding lemma, and [Agrawal–Rosen, *Online-Offline Functional Encryption for Bounded Collusions*, Lemma 2.4](https://www.cse.iitd.ac.in/~shweta/papers/AR16.pdf) state a discrete-Gaussian drowning bound in a Ring-LWE context. Those are discrete bounds on specified laws; the present question is the optimum over every Euclidean additive noise law at a specified second moment, in an unwrapped real space. If an independent shift is a random variable supported in the \(h\)-ball, convexity gives the same guarantee as for fixed shifts, and a deterministic postprocessing such as wrapping cannot increase this TV. There is no asserted converse after wrapping, no particular scheme parameter improvement, and no claim about discrete or finite-precision sampling.

Run the companion `verify-euclidean-smudging-optimum.py` with Python and SciPy. The computations check the explicit formulas on generated inputs; the conclusions are proved analytically above.
