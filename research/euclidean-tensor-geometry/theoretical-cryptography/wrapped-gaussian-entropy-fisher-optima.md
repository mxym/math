# Exact lattice optima for wrapped Gaussian entropy and short-time Fisher volume

Let \(\Lambda\subset\mathbb R^n\) have covolume one. Write
\[
\phi_t(x)=(4\pi t)^{-n/2}e^{-|x|^2/(4t)},\qquad
p_{t,\Lambda}(x)=\sum_{v\in\Lambda}\phi_t(x+v).
\]
On \(\mathbb R^n/\Lambda\) this is the heat-kernel density relative to Haar probability. Consider its relative entropy \(D_t(\Lambda)=\int p_{t,\Lambda}\log p_{t,\Lambda}\) and the normalized Fisher volume
\[
V_t(\Lambda)=\sqrt{\det\left(2t\int p_{t,\Lambda}
\nabla\log p_{t,\Lambda}\otimes\nabla\log p_{t,\Lambda}\right)}.
\]

**Theorem.** In dimension two the area-one triangular lattice uniquely minimizes \(D_t\) over all area-one lattices for all sufficiently small \(t>0\) and for all sufficiently large \(t\). It also uniquely maximizes \(V_t\) over all area-one lattices for all sufficiently small \(t>0\). These are exact optimizers for each time in the respective range, not just limiting shapes. The same three conclusions hold for \(E_8\) in dimension 8 and the Leech lattice in dimension 24. Uniqueness is up to isometry.

The proof uses the following general assumptions on a covolume-one lattice \(\Gamma\) in the given dimension: it uniquely maximizes the shortest-vector length; its normalized shortest vectors form a spherical 4-design; its isometry group acts transitively on them. In this generality the small-time optimizer in both statements is \(\Gamma\), while the large-time entropy optimizer is \(\Gamma^*\). The named examples are isodual.

## 1. Localization of a nearly optimal shortest length

Set \(m=\lambda_1(\Gamma)^2\) and let \(M\) be the full signed shortest shell. In a neighborhood of the isometry class of \(\Gamma\), a lattice can be represented as \(e^{S/2}\Gamma\), with \(S\) a small trace-free real symmetric matrix, by polar decomposition of a nearby basis. Write \(q_S(v)=v^\top e^S v\). The design property gives, for trace-free symmetric \(B\),
\[
\sum_{v\in M}v^\top Bv=0,\qquad
\sum_{v\in M}(v^\top Bv)^2
=\frac{2|M|m^2}{n(n+2)}\|B\|_{\rm F}^2.
\]
In particular \(\min_{v\in M}v^\top Bv\le-\kappa\|B\|_{\rm F}\) for a constant \(\kappa>0\): on the compact unit sphere a minimum of zero would force all the summands to vanish. Since \(q_S(v)=m+v^\top Sv+O(\|S\|_{\rm F}^2)\) uniformly on the finite shell, the shortest square length of \(e^{S/2}\Gamma\) is at most \(m-\kappa\|S\|_{\rm F}/2\), for sufficiently small \(S\). Mahler compactness (on fixed covolume and systole bounded away from zero) and uniqueness ensure that all lattices with \(m-\lambda_1(\Lambda)^2\) sufficiently small lie in this chart. Consequently
\[
m-\lambda_1(\Lambda)^2\le C\epsilon
\quad\Longrightarrow\quad
\Lambda\simeq e^{S/2}\Gamma,\quad \|S\|_{\rm F}\le C'\epsilon
\]
for sufficiently small \(\epsilon\).

Any differentiable isometry-invariant lattice functional is stationary in the shape variable at \(S=0\). In fact its gradient there is trace free and fixed by conjugation by \(\operatorname{Aut}(\Gamma)\); its quadratic forms on the shortest shell are therefore all equal by transitivity, all zero by the design mean, and the gradient is zero by the second identity. This is an exact stationarity assertion, not an asymptotic one.

## 2. Two-image kernels with differentiated error bounds

Let \(X\) have density \(\phi_t\), \(Y=X\bmod\Lambda\), and
\(z_v(x)=\phi_t(x+v)/\phi_t(x)\) for \(v\in\Lambda\setminus\{0\}\).
The part of \(D_t\) that depends on the lattice is
\[
W_t(\Lambda)=D_t(\Lambda)+\frac n2\log(4\pi e t)
=\mathbb E\log\!\left(1+\sum_{v\ne0}z_v(X)\right).
\]
This follows by unfolding \(\int p\log p\) to \(\int_{\mathbb R^n}\phi_t(x)\log p_{t,\Lambda}(x)\,dx\). The quantity \(W_t\) is also the conditional Shannon entropy of the lattice label of the lift given \(Y\), for any fixed choice of representatives.

For Fisher volume put \(Q_t=I-2t\int p\nabla\log p\otimes\nabla\log p\); then \(0\preceq Q_t\preceq I\) and
\[
Q_t=\frac{1}{2t}\mathbb E\operatorname{Cov}(X\mid Y)
=\frac{1}{4t}\sum_{v\ne0}vv^\top\,\mathbb E\frac{z_v(X)}{1+\sum_{w\ne0}z_w(X)}.
\]
The first equality follows from the score \(-\mathbb E[X\mid Y]/(2t)\) and total covariance. For the second equality, expand the covariance of the posterior weights as half the sum over ordered pairs of weights times the tensor square of the pair difference, then unfold one weight to the full Gaussian density. This is the posterior identity used in [Cho–Jang, Proposition 16.1](https://arxiv.org/abs/2610.37520).

For a single vector of length \(r\) define
\[
B_t(r)=\mathbb E\log(1+z_v(X)),\qquad C_t(r)=\mathbb E[z_v(X)/(1+z_v(X))].
\]
Using the longitudinal coordinate \(X\cdot v/r=-r/2+(2t/r)u\) gives
\[
(B_t(r),C_t(r))=\frac{\sqrt t}{\sqrt\pi r}e^{-r^2/(16t)}
\int_{\mathbb R} e^{-tu^2/r^2+u/2}
\left(\log(1+e^{-u}),\frac{1}{1+e^u}\right)\,du .
\]
The integrals at \(t=0\) are \(2\pi\) and \(\pi\). For the second, substitute \(z=e^u\); for the first, substitute \(z=e^{-u}\) and integrate by parts. Both integrands at \(t=0\) have integrable polynomial moments of every order. In particular the prefactors after removing \(\sqrt t e^{-r^2/(16t)}\) approach \(2\sqrt\pi/r\) and \(\sqrt\pi/r\), with error \(O(t)\) in \(C^2\) as functions of \(r^2\) on compact subintervals of \((0,\infty)\).

**Pair approximation with shape derivatives.** In the chart \(e^{S/2}\Gamma\) on a sufficiently small but fixed neighborhood of zero, \(W_t\) is \(\sum_{v\ne0}B_t(|v|)\) with a remainder bounded in \(C^2_S\) by \(O(e^{-(m/16+\delta)/t})\) for some \(\delta>0\). Likewise \(Q_t\) is \(\frac1{4t}\sum_{v\ne0}vv^\top C_t(|v|)\) with such a remainder. Here and below lattice vectors inside these sums are transported by \(e^{S/2}\).

To prove the two estimates, at a fixed \(x\) put \(a_v=\log z_v\), \(p_v=z_v/(1+z_v)\), \(r_v=z_v/(1+\sum z_w)\). Finite sums may be used first. For the entropy error the pointwise difference of \(\sum\log(1+z_v)\) and \(\log(1+\sum z_v)\) is nonnegative, and is bounded above by the sum over distinct unordered pairs of \(\min\{\log(1+z_v),\log(1+z_w)\}\): the log of the sum of images is at least the largest individual log. The pair minimum is bounded by \(C(z_vz_w)^{1/4}\), using \(\log(1+z)\le C\sqrt z\). The first partial derivative of this difference with respect to \(a_v\) is \(p_v-r_v=\sum_{w\ne v}p_vr_w\). Its second derivatives are \((p_v-r_v)(1-p_v-r_v)\) on the diagonal and \(r_v r_w\) off it. All these terms are bounded by the same double-pair weights, since \(p_v\le\min(1,z_v)\) and \(r_w\le\min(1,z_w)\).

For the Fisher error use \(p_v-r_v=\sum_{w\ne v}p_vr_w\) directly and differentiate this product up to twice in \(S\). Its derivative bounds keep the factor \(p_v r_w\), with polynomial losses in \(t^{-1},|x|,|v|,|w|\). Indeed \(\partial p_v=p_v(1-p_v)\partial a_v\), and
\(\partial r_w=r_w(\partial a_w-\sum_jr_j\partial a_j)\). Differentiating these identities once more only involves posterior averages of polynomials. Such averages in \(|j|\) are bounded by polynomials in \(1+|x|\), uniformly here for \(t\le1\): use \(\sum_j r_j\le1\) for \(|j|\le4|x|+1\), and \(r_j\le z_j\le e^{-|j|^2/(8t)}\) outside. Shape derivatives of \(a_v\) up to second order are bounded by \(C t^{-1}(|v|^2+|x||v|)\). The outer \(vv^\top\) and its derivatives also contribute only polynomials.

The exact average of the double-pair weight is
\[
\mathbb E[(z_vz_w)^{1/4}]
=\exp\!\left(-\frac{2(|v|^2+|w|^2)+|v-w|^2}{64t}\right).
\]
This is Gaussian completion of the square; the tilted Gaussian is centered at \(-(v+w)/4\), so any additional polynomial in \(|x|\) costs only a polynomial in \(|v|,|w|\) and \(t^{-1}\). The numerator is at least \(5\lambda_1(e^{S/2}\Gamma)^2\) for distinct nonzero \(v,w\). Requiring \(\lambda_1(e^{S/2}\Gamma)^2\ge0.95m\), use nine tenths of the numerator for the uniform exponential gain \(0.9\cdot 5\cdot0.95m>4m\), and the remaining tenth for summability of the two Gaussian lattice tails with any fixed polynomial weight. Absorb powers of \(1/t\) into part of the strict gain. This proves the bounds. Termwise differentiations can equivalently be made with finite image sets and then passed to the limit: on compact \(x\)-sets all Gaussian sums converge with shape derivatives; on the whole space the near and far image split gives polynomial majorants in \(|x|\) for the integrands and the differentiated posterior sums (with fixed powers of \(1/t\)). The displayed pair bound is summable uniformly in the shape neighborhood.

## 3. Exact small-time optima

First localize candidates without excluding collapsing lattices. If \(r=\lambda_1(\Lambda)\ge\sqrt t\), \(W_t(\Lambda)\ge B_t(r)\) and the formula for \(B_t\), restricted to \(0\le u\le 1\), gives
\(W_t(\Lambda)\ge c\sqrt t\,e^{-r^2/(16t)}\), with \(c>0\) independent of \(\Lambda\) by \(r\le\sqrt m\). If \(r<\sqrt t\), then on the half space \(X\cdot v\le0\) one has \(z_v(X)\ge e^{-1/4}\), so \(W_t\) is bounded below by a positive constant. At \(\Gamma\) the pair approximation and the positive gap to the next shell give \(W_t(\Gamma)=O(\sqrt t\,e^{-m/(16t)})\). Thus any candidate no worse than \(\Gamma\) must have \(m-r^2=O(t)\).

For Fisher volume set \(d_t=1-V_t\). Since \(0\preceq Q_t\preceq I\), the determinant bound \(\sqrt{\det(I-Q_t)}\le e^{-\operatorname{tr}Q_t/2}\) gives \(d_t\ge c_n\operatorname{tr}Q_t\). One can lower bound \(\operatorname{tr}Q_t\) using **any** nonzero lattice vector \(v\) of length \(r\). An estimator \(b(Y)\) of \(X\) has the same squared risk if its integral is written at \(x+v\) rather than at \(x\), since the two wrapped \(Y\)'s coincide. Averaging the two expressions and minimizing the common estimator pointwise gives the lower bound \((r^2/2)C_t(r)\) on the risk. Apply it to the posterior mean, so \(\operatorname{tr}Q_t\ge(r^2/(4t))C_t(r)\). For \(r=\lambda_1(\Lambda)\ge\sqrt t\) this yields \(d_t\ge c(r/\sqrt t)e^{-r^2/(16t)}\). If \(r<\sqrt t\), take an integer multiple of a shortest vector of length in \([\sqrt t,2\sqrt t]\); then \(d_t\ge c'>0\). At \(\Gamma\) the pair approximation gives \(d_t(\Gamma)=O(t^{-1/2}e^{-m/(16t)})\). A competitor no worse than \(\Gamma\) must therefore have \(r\ge\sqrt m/2\) for sufficiently small \(t\) (if \(\sqrt t\le r\le\sqrt m/2\) the exponential decay is at most \(e^{-m/(64t)}\)). With that lower bound on \(r\), the two prefactors \(t^{-1/2}\) match, and \(m-r^2=O(t)\) as well.

For either functional, localization in §1 now gives \(S=tZ\) with \(\|Z\|_{\rm F}\le C\). On any fixed bounded \(Z\)-ball,
\[
\begin{aligned}
t^{-1/2}e^{m/(16t)} W_t(e^{tZ/2}\Gamma)&\longrightarrow
\frac{2\sqrt\pi}{\sqrt m}\sum_{v\in M} e^{-v^\top Zv/16},\\
t^{1/2}e^{m/(16t)} d_t(e^{tZ/2}\Gamma)&\longrightarrow
\frac{\sqrt{\pi m}}{8}\sum_{v\in M} e^{-v^\top Zv/16}
\end{aligned}
\qquad\text{in } C^2_Z.
\]
For the first limit apply §2 and \(q_{tZ}(v)=m+t\,v^\top Zv+O_{C^2_Z}(t^2)\) on \(M\). The next-shell gap at \(\Gamma\) and a uniform Gaussian tail bound make all other single-vector terms exponentially smaller, with derivatives as well; the single-vector integral prefactors and their derivatives are uniformly polynomially bounded for \(r\) bounded below. For the second limit use the same argument for \(Q_t\), and \(1-\sqrt{\det(I-Q)}=\frac12\operatorname{tr}Q+O(\|Q\|^2)\) with its analytic derivative estimates near zero.

The limiting Hessian of either displayed function exceeds a positive multiple of the identity on the whole fixed \(Z\)-ball: differentiate the exponential sum twice and use the shortest-shell squared-form identity. Therefore the actual normalized functional is strictly convex there for all sufficiently small \(t\). By exact stationarity at \(Z=0\), its unique minimum is at zero. Together with localization this proves the claimed global optima, including against degenerating tori.

## 4. Exact large-time entropy optimum

Use the reciprocal lattice, write \(a=4\pi^2t\), and let \(r=\lambda_1(\Lambda^*)\). The Fourier series of \(p_{t,\Lambda}\) has mean one and nonzero coefficients \(e^{-a|\xi|^2}\), \(\xi\in\Lambda^*\). A real cosine of a shortest frequency is a test bounded by one, so \(\|p-1\|_1\ge e^{-ar^2}\). Hence \(D_t(\Lambda)\ge\frac12 e^{-2ar^2}\) by Pinsker's inequality. At \(\Lambda=\Gamma^*\), Taylor expansion about 1 and the Gaussian dual tail give \(D_t(\Gamma^*)=O(e^{-2am})\). Thus a candidate no worse than this has \(m-r^2=O(a^{-1})\), yielding \(\Lambda^*\simeq e^{Z/(2a)}\Gamma\), \(\|Z\|_{\rm F}\le C\).

Pull the direct torus back to the fixed torus \(\mathbb R^n/\Gamma^*\) by \(e^{-Z/(2a)}\). Its Fourier characters are then fixed, with coefficients \(e^{-a q_{Z/a}(v)}\). On bounded \(Z\)-balls, \(p-1\) is \(O(e^{-am})\) in uniform norm with two \(Z\)-derivatives by Gaussian summation. The entropy is \(\frac12\int(p-1)^2\) plus an \(O(e^{-3am})\) remainder with the same derivatives. Parseval therefore yields
\[
e^{2am}D_t(e^{-Z/(2a)}\Gamma^*)\longrightarrow \tfrac12\sum_{v\in M} e^{-2v^\top Zv}
\qquad\text{in }C^2_Z.
\]
As before there is a uniformly positive limiting Hessian and the exact functional is stationary at zero. This proves global strict optimality for sufficiently large \(t\).

## Scope and comparison

The elementary planar reduced-basis argument gives the unique area-one packing optimum \(\Gamma=A_2\) with \(m=2/\sqrt3\): a shortest length \(r\) has a completing vector with component in its direction at most \(r/2\) in absolute value and orthogonal component \(1/r\), so \(r^2\le r^2/4+1/r^2\); equality forces the triangular lattice. Its signed shortest shell is a regular hexagon, hence a 4-design and transitive. Its covolume-one dual is isometric to itself, as is the dual of any area-one planar lattice by quarter-turn. For \(E_8\) and the Leech lattice use [Cohn–Kumar's uniqueness among lattices](https://annals.math.princeton.edu/2009/170-3/p01), the spherical 7- and 11-design properties of the respective minimal shells (see [Cohn–Kumar on spherical designs and sharp configurations](https://arxiv.org/abs/math/0607446)), and transitivity of the Weyl group on the \(E_8\) roots and of the Leech automorphism group on its minimal shell (also recorded in Cohn–Kumar's uniqueness paper). Both are self-dual.

[Montgomery's minimum-theta theorem](https://doi.org/10.1017/S0017089500007047) gives the planar minimum for the quadratic heat-kernel distance to Haar at *every* time, by Parseval. That linear Gaussian lattice sum is not the nonlinear relative entropy or Fisher volume. [Cho–Jang, Corollary 16.3](https://arxiv.org/abs/2610.37520) prove convergence of short-time Fisher optimizers to the triangular lattice, explicitly distinguishing it from exact optimality for each small positive time. The \(C^2\) estimate in §2 and exact stationarity supply that stronger statement; the lower bound also covers collapsing lattices. The two-image entropy constant parallels the [finite-constellation high-SNR asymptotics of Alvarado et al.](https://arxiv.org/abs/1212.6526); here the full infinite lattice, differentiated error, and the optimization over shapes are part of the conclusion. No all-time entropy claim is made. The Fisher result is only for the short-time range; large-time hexagonal *maximality* is false already in dimension two by Cho–Jang's comparison (Remark 16.5). This is an optimization theorem for continuum torus measures, not an attack on or analysis of a specific cryptographic scheme.

Replay: `node verify-wrapped-gaussian-entropy-fisher-optima.js` (Node.js 18+, no dependencies or data). Its finite integer checks validate the planar shell and pair-exponent identities. Independent direct-image and reciprocal-space quadratures are numerical sanity checks only; the optimization is proved by the shape derivative estimates above.
