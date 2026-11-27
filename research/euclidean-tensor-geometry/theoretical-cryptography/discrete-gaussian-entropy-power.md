# Strict reverse entropy power for centered lattice Gaussians

Let \(L\subset\mathbb R^n\) be a fixed full-rank Euclidean lattice. Let \(X_v\) have distribution \(\mu_v\) on \(L\) proportional to \(\exp(-\|x\|^2/(2v))\), with variance parameter \(v>0\). Its actual second moment need not be \(n v\). For a law \(P\) on \(L\) define the normalized Shannon entropy power
\[
\mathcal N(P)=\frac{(\det L)^{2/n}}{2\pi e}\exp\left(\frac{2H(P)}{n}\right)
\]
using natural logarithms and the covolume \(\det L\). The constant simply puts the large-width entropy power of \(\mu_v\) on the scale \(v\).

**Theorem.** For independent \(X_v,X_w\) and all \(v,w>0\),
\[
\mathcal N(\mu_v*\mu_w)<\mathcal N(\mu_v)+\mathcal N(\mu_w).
\tag{1}
\]
The same strict conclusion holds with any finite number of at least two independent centered Gaussians on one lattice with a common positive-definite Gaussian shape and arbitrary positive scale multipliers. A common shape is necessary for such a general result.

Write \(\lambda=\lambda_1(L^*)\) and let \(N\) be the number of vectors of length \(\lambda\) in \(L^*\), counting signs. Put \(\beta=2\pi^2\lambda^2\). The strictly positive defect in (1) satisfies the uniform sharp expansion
\[
\mathcal N(\mu_v)+\mathcal N(\mu_w)-\mathcal N(\mu_v*\mu_w)
=\frac{2N}{n}\,v e^{-\beta v}
\left[(1+e^{-\beta(w-v)/2})^2+O_L(v^{-1})\right]
\tag{2}
\]
as \(v\to\infty\), uniformly over all \(w\ge v\), with no upper bound on the ratio \(w/v\). In particular the normalized leading coefficient is four at equal widths and tends to one when the absolute variance-parameter difference goes to infinity.

The strict inequality concerns this family of discrete Gaussian masses, not arbitrary lattice distributions or continuous Gaussians. It uses the same entropy-power functional as the continuous inequality, but uses Shannon entropy on the given lattice.

## 1. The entropy envelope and the all-scale inequality

Let \(Z_v=\sum_{x\in L}e^{-\|x\|^2/(2v)}\), and write
\[
Z_v=\frac{(2\pi v)^{n/2}}{\det L}\exp(F(v)),\qquad
F(v)=\log\left(1+\sum_{\ell\in L^*\setminus\{0\}}e^{-2\pi^2 v\|\ell\|^2}\right)
\]
by Poisson summation. For the actual moment \(m(v)=\mathbb E\|X_v\|^2\), logarithmic differentiation gives
\[
m(v)=n v+2v^2F'(v)<n v,
\tag{3}
\]
strict because \(F'(v)<0\). On the other hand \(m'(v)=\operatorname{Var}_{\mu_v}(\|X_v\|^2)/(2v^2)>0\). The range of \(m\) is \((0,\infty)\), by the discrete small-width limit and by Poisson summation at large width.

For each \(m>0\) let \(v_m\) be the unique parameter matching \(m\). The variational entropy identity for any probability \(P\) on \(L\) of moment \(m\) is
\[
H(P)=H(\mu_{v_m})-D(P\Vert\mu_{v_m}).
\tag{4}
\]
Indeed the cross-entropy is \(m/(2v_m)+\log Z_{v_m}\), the same for every such \(P\). The finite second moment bounds entropy from above by this cross-entropy, and all the quantities in (4) are finite. In particular \(E(m)=\mathcal N(\mu_{v_m})\) is the maximum entropy power at moment \(m\).

From \(H(\mu_v)=\log Z_v+m(v)/(2v)\), differentiating in \(m\) gives \(dH/dm=1/(2v_m)\), so
\[
\frac{d}{dm}\frac{E(m)}m
=\frac{E(m)}{m^2}\left(\frac{m}{nv_m}-1\right)<0
\]
by (3). Consequently \(E(m_1+m_2)<E(m_1)+E(m_2)\) for positive \(m_1,m_2\): multiply the strict ratio comparisons by \(m_1,m_2\) and add. For the centered independent Gaussians the second moments add, and (4) proves (1). The same argument applies to more than two summands directly, by comparing each \(m_i\) to the total. For a common quadratic shape, simultaneously transform the lattice and all laws by its inverse square root and apply the same argument; entropy is invariant under that bijective change, and the covolume normalization multiplies every entropy power by the same positive factor.

## 2. The envelope's contributions to the asymptotic defect

Write \(T=v+w\), \(u=vw/T\), \(a=v/T\), and let \(V\) be the variance parameter matching the second moment of the convolution, so \(m(V)=m(v)+m(w)\). For fixed \(L\), discreteness of its dual lengths and Gaussian tail summation give, for some \(\epsilon_L>0\),
\[
F(x)=N e^{-\beta x}+O_L(e^{-(\beta+\epsilon_L)x}),\qquad
F'(x)=-\beta N e^{-\beta x}+O_L(e^{-(\beta+\epsilon_L)x})
\quad (x\to\infty).
\]
These estimates follow by splitting off the shortest shell in the dual sum; a factor of \(\|\ell\|^2\) for the derivative preserves an exponential gap after decreasing \(\epsilon_L\) if necessary. The logarithm's second-order correction is also exponentially smaller. With perhaps a further decreased \(\epsilon_L>0\), (3) and the entropy formula imply
\[
\delta(x):=\mathcal N(\mu_x)-m(x)/n
= \frac{2N}{n} x e^{-\beta x}
  +O_L\bigl(x e^{-(\beta+\epsilon_L)x}\bigr).
\tag{5}
\]
Here \(\mathcal N(\mu_x)=x\exp((2/n)(F(x)+xF'(x)))\); the linear \(xF'(x)\) term cancels in subtracting the moment. The discarded quadratic and higher terms are \(O_L(x^3e^{-2\beta x})\) and can be absorbed by decreasing \(\epsilon_L\).

Uniformly over \(w\ge v\to\infty\), (3) and \(m'(x)=n+o(1)\) give
\[
V=T+O_L(v^2e^{-\beta v}),\qquad
\mathcal N(\mu_V)=T(1+O_L(v e^{-\beta v})).
\tag{6}
\]
Indeed each of \(v,w,T\) has its own moment correction bounded by \(C_L x^2e^{-\beta x}\), which is decreasing for large \(x\); use the inverse moment function with derivative bounded on the large-parameter range. The estimate on \(m'\) follows from differentiating the dual sums a second time. Let \(P=\mu_v*\mu_w\) and \(D_V=D(P\Vert\mu_V)\). By (4), the defect admits the exact decomposition
\[
\mathcal N(\mu_v)+\mathcal N(\mu_w)-\mathcal N(P)
=\delta(v)+\delta(w)-\delta(V)
+\mathcal N(\mu_V)(1-e^{-2D_V/n}).
\tag{7}
\]
The first three terms, divided by \((2N/n)v e^{-\beta v}\), give
\[
1+e^{-\beta(w-v)}+O_L(v^{-1})
\tag{8}
\]
uniformly. The \(\delta(V)\) contribution is exponentially small by \(V\ge2v-O_L(v^2e^{-\beta v})\). For \(\delta(w)\) the prefactor \(w/v\) can be replaced by one with the indicated error, since \((w-v)e^{-\beta(w-v)}/v=O_L(1/v)\).

## 3. The convolution's contribution, including the balanced transition

Completing the square in the convolution and applying Poisson to the shifted inner lattice Gaussian gives the likelihood ratio against \(\mu_T\):
\[
\frac{P(z)}{\mu_T(z)}
=\frac{M_u(a z)}{\mathbb E_{\mu_T} M_u(a Z)},\qquad
M_u(y)=\sum_{\ell\in L^*}e^{-2\pi^2 u\|\ell\|^2}e^{2\pi i\langle\ell,y\rangle}.
\tag{9}
\]
Here \(Z\sim\mu_T\) in the denominator. In fact the product of the two exponents separates into \(-\|z\|^2/(2T)-\|x-a z\|^2/(2u)\), and the proportionality factor is fixed by normalization. The nonzero terms of the real function \(M_u\) come in opposite pairs. Since \(u\ge v/2\), \(\|M_u-1\|_\infty=O_L(e^{-\beta u})\) uniformly. The Taylor expansion of \(r\log r\) about \(r=1\), with the linear term integrating to zero for the likelihood ratio \(r\), yields
\[
D(P\Vert\mu_T)
=\tfrac12\operatorname{Var}_{\mu_T}\big(M_u(a Z)\big)\bigl(1+O_L(e^{-\beta u})\bigr).
\tag{10}
\]
The relative error bound holds even when the variance is small: the pointwise cubic remainder is bounded by \(C\|r-1\|_\infty (r-1)^2\), and the denominator in (9) is \(1+O_L(e^{-\beta u})\).

By the matched second moment,
\[
D_V=D(P\Vert\mu_T)-D(\mu_V\Vert\mu_T).
\tag{11}
\]
The last term is at most \(C_L (V-T)^2/T^2\). For example, in the precision parameter \(p=1/(2v)\), the log partition has second derivative \(\operatorname{Var}(\|X_v\|^2)=O_L(T^2)\) for \(v\) between \(V,T\); the precision difference is \(O(|V-T|/T^2)\). This gives the bound by the second-order formula for the relative entropy of that exponential family. The fourth-moment bound follows by Poisson differentiation or a Gaussian Riemann sum. By (6), \(T D(\mu_V\Vert\mu_T)=O_L(v^3 e^{-2\beta v})\). Thus this refitting correction is negligible compared to \(v e^{-\beta v}/v\).

Put \(d=w-v\). For \(0\le d\le v\) we will use approximate parity:
\[
\operatorname{Var}_{\mu_T}(M_u(a Z))
=e^{-2\beta u}\left(2N+O_L(d^2/v+e^{-c_L v})\right)
\tag{12}
\]
for some \(c_L>0\). To see this, let \(S\) be the shortest dual shell and write \(B(Z)=\sum_{\ell\in S}e^{2\pi i a\langle\ell,Z\rangle}\). Its real value can be compared to \(B_0(Z)=\sum_{\ell\in S}(-1)^{\langle\ell,Z\rangle}\). Since \(\langle\ell,Z\rangle\) is an integer, each paired cosine differs from the parity cosine by at most \(C|a-\tfrac12|^2|\langle\ell,Z\rangle|^2\). Hence \(\|B-B_0\|_{L^2(\mu_T)}=O_L(d^2/v)\): \(a-\frac12=-d/(2T)\), and the fourth moment is \(O_L(T^2)\). Both \(B\) and \(B_0\) are bounded by \(N\), so this estimate also controls their variance difference. The parity characters become uniform in mean on \(L/2L\) up to \(O_L(e^{-c_L T})\) by Poisson: for a nontrivial parity frequency \(\ell/2\bmod L^*\), the dual Gaussian sum is over a fixed translate at positive distance from zero. In particular each shortest \(\ell\) gives a nontrivial bit, and two shortest vectors give the same bit exactly for an antipodal pair or equality. Indeed, if \(\ell\) and \(m\) are in the same class of \(2L^*\) and not equal or opposite, both \((\ell+m)/2\) and \((\ell-m)/2\) are nonzero dual vectors whose squared lengths sum to \(\lambda^2\), contradicting the minimum. Thus the limiting variance of \(B_0\) is \(2N\). In (9), the higher shells, after extracting \(e^{-\beta u}\), are \(O_L(e^{-\epsilon_L u})\) uniformly. This proves (12).

For large disparity we also need a different uniform estimate to keep the variance controlled when \(T/v\) is unbounded:
\[
\operatorname{Var}_{\mu_T}(M_u(a Z))
\le C_L e^{-2\beta u}\min(1,v^4/T^2).
\tag{13}
\]
The first bound follows from the sup norm of \(M_u-1\). For the second compare \(M_u(aZ)\) to \(M_u(0)\), pair opposing frequencies, use \(1-\cos x\le x^2/2\), and sum the additional factor \(\|\ell\|^2\) over the dual Gaussian. The pointwise difference is at most \(C_L e^{-\beta u} a^2\|Z\|^2\), and squaring and averaging yields the other bound since \(a=v/T\).

By (10) and (13), \(D_V\to0\) exponentially in \(v\). After dividing the final term in (7) by \((2N/n)v e^{-\beta v}\), we may replace \(\mathcal N(\mu_V)\) by \(T\) and \(1-e^{-2D_V/n}\) by \(2D_V/n\), with exponentially small normalized error: \(T D_V/(v e^{-\beta v})\) is uniformly bounded, by the estimates below. For \(d\le v\), use (10)–(12). Then
\[
\frac{T D_V}{N v e^{-\beta v}}
= \frac T v e^{-\beta(2u-v)}+O_L(v^{-1})
= 2e^{-\beta d/2}+O_L(v^{-1}).
\tag{14}
\]
For the errors here, \(2u-v=vd/T\ge d/3\); the order \(d^2/v\) variance error is multiplied by \(O(e^{-\beta d/3})\) so is \(O_L(v^{-1})\). The exponent \(vd/T\) differs from \(d/2\) by \(d^2/(2T)\), yielding the same bound after multiplying by \(e^{-\beta d/3}\). The prefactor \(T/v=2+d/v\) likewise gives only \(O_L(v^{-1})\) error. For \(d>v\), \(2u-v\ge v/3\). Now (10), (11), and (13) bound the left side of (14) by
\[
C_L e^{-\beta v/3}\min(T/v,v^3/T)\ \le\ C_L v e^{-\beta v/3},
\]
and its asserted main term is also exponentially small. Hence (14) is uniform without controlling \(w/v\). Adding (8) and (14) in (7) proves (2).

## Scope and relation to existing results

A common shape cannot be dropped. For example take \(L=\mathbb Z^2\), a fixed \(c>1\), and independent product Gaussians with coordinate variance parameters \((v,cv)\) and \((cv,v)\). Each input has normalized entropy power asymptotic to \(\sqrt c\,v\) by the one-dimensional Poisson formula and product entropy. The output has two independent copies of the same one-dimensional convolved law and entropy power asymptotic to \((1+c)v\) by (2) in dimension one. Since \(1+c>2\sqrt c\), the reverse inequality fails there for sufficiently large \(v\).

[Haghighatshoar–Abbe–Telatar, *A New Entropy Power Inequality for Integer-Valued Random Variables*](https://arxiv.org/abs/1301.4185) study different lower bounds for entropy growth under lattice addition. The result here is an upper bound on the usual continuous-style entropy-power functional for this particular family, not a replacement for their general discrete inequalities. [Harremoës–Vignat, *An Entropy Power Inequality for the Binomial Family*](https://emis.muni.cz/journals/JIPAM/images/043_03/043_03.pdf) give a special discrete family satisfying the forward inequality, also consistent with the restricted scope here. The convolution identity in (9) is the standard completing-square ingredient in discrete Gaussian analyses such as [Genise–Micciancio–Peikert–Walter](https://web.eecs.umich.edu/~cpeikert/pubs/gaussians.pdf). The all-scale monotonic envelope and the relative asymptotic defect, with the balanced parity transition, are the claims analyzed here.

Replay with `node verify-discrete-gaussian-entropy-power.js`. The last run passed 18,939 exact completion-of-squares and parity-shell checks, and 1,092 numerical checks, including direct convolutions and stable large-disparity estimates.
