# Integer energy shells versus independent discrete Gaussians

Let \(P_t\) on \(\mathbb Z\) have masses \(e^{-t j^2}/\theta(t)\) for \(t>0\). Let \(X\sim P_t\), \(Y=X^2\), \(r(t)=\mathbb E_tY\), and \(\sigma(t)^2=\operatorname{Var}_tY\). For an integer \(E>0\) and \(n\ge4\), let \(U_{n,E}\) be uniform on \(\{x\in\mathbb Z^n:\sum x_i^2=E\}\), with marginal \(U_{n,E}^{(k)}\) on \(k\) coordinates. Select \(t=t_{n,E}\) by \(r(t)=E/n\): \(r'(t)=-\sigma(t)^2<0\), and the endpoint limits of \(r(t)\) are \(+\infty,0\). We compare \(U_{n,E}^{(k)}\) to \(P_t^{\otimes k}\) using total variation, defined as half the \(\ell^1\) distance.

## Main statements

Write \(a=k/n\), \(M=\min(n,E)\), and
\[
B(a)=d_{\rm TV}\big(N(0,1-a),N(0,1)\big).
\]
Here \(B(0)=0,\ B(1)=1\); for \(0<a<1\),
\[
B(a)=2\big[\Phi(z_a/\sqrt{1-a})-\Phi(z_a)\big],
\qquad
z_a^2=-\frac{1-a}{a}\log(1-a).
\tag{1}
\]

1. For every sequence \(n\to\infty,\ E=E_n\to\infty\), of arbitrary relative growth, if \(a\to\alpha\) then
\[
d_{\rm TV}(U_{n,E}^{(k)},P_t^{\otimes k})\longrightarrow B(\alpha).
\tag{2}
\]
On closed subintervals of \(0<a<1\), the distance is \(B(a)+O(M^{-1/2})\), with a constant depending only on the subinterval. If \(a\to0\) and \(aM\to\infty\), it is asymptotic to \(\varphi(1)k/n\), where \(\varphi\) denotes the standard normal density.
2. If \(E=e\) is a positive fixed integer, then, uniformly in \(k\),
\[
d_{\rm TV}(U_{n,e}^{(k)},P_t^{\otimes k})
=d_{\rm TV}\big(\operatorname{Bin}(e,a),\operatorname{Poi}(ae)\big)+O_e(n^{-1}).
\tag{3}
\]
For zero energy both laws can be taken to be the point mass at zero. The bounded-energy formula is different from (2), even at the same limiting observed fraction.
3. If \(E_n\to\infty\) and \(a\to\alpha\in(0,1)\), the limit \(B(\alpha)\) is optimal among all precision retunings \(P_s^{\otimes k}\), \(s>0\). More precisely, let \(h_n=(s_n-t)\sigma(t)\sqrt{k}\). If \(h_n\to h\in\mathbb R\), the limiting distance is
\[
d_{\rm TV}\big(N(0,1-\alpha),N(-h,1)\big).
\tag{4}
\]
If \(|h_n|\to\infty\), the limit is \(1\). The infimum over \(s>0\) therefore tends to \(B(\alpha)\), and attaining this value asymptotically requires \(h_n\to0\).

The measures are unwrapped, independent before conditioning, and have no algebraic modulus or secret. The exact energy constraint models a global dependence that can be invisible to a small coordinate marginal.

## A uniform lattice Edgeworth estimate

Write \(\rho(t)=\min(1,r(t))\). For independent copies of \(Y\) under precision \(t\), set \(p_{m,t}(j)=\Pr_t(\sum_{i=1}^mY_i=j)\). For \(h=(j-mr(t))/(\sigma(t)\sqrt m)\), uniformly in \(t>0\) and \(j\in\mathbb Z\) as \(m\rho(t)\to\infty\),
\[
\sigma(t)\sqrt m\,p_{m,t}(j)
= \varphi(h)+\frac{\gamma_3(t)}{6\sqrt m}(h^3-3h)\varphi(h)
+O\big((m\rho(t))^{-1}\big),
\quad
\gamma_3(t)=\frac{\mathbb E_t[(Y-r(t))^3]}{\sigma(t)^3}.
\tag{5}
\]
We give details to handle both degenerate limits of the parameter.

For \(0<t\le1\), \(\sigma(t)\asymp t^{-1}\), and \(\rho(t)\) is bounded away from zero. This follows from Riemann sums: \(\sqrt t X\) tends, with all fixed moments, to the real density \(\pi^{-1/2}e^{-x^2}\) as \(t\downarrow0\), with Gaussian tails bounding each polynomial moment; compactness handles the rest. For \(t\ge1\), write \(q=e^{-t}\). The masses of \(Y=0\) and \(Y=1\) are bounded below by \(c\) and \(cq\), respectively. The fixed positive moments of \(Y\) are \(O(q)\), by summing \(j^{2p}e^{-tj^2}\). Thus \(r(t)\asymp q\), \(\sigma(t)^2\asymp q\), and \(\rho(t)\asymp q\). These facts give the uniform moment bounds
\[
\mathbb E_t|Y-r(t)|^3\le C\sigma(t)^3/\sqrt{\rho(t)},\qquad
\mathbb E_t|Y-r(t)|^4\le C\sigma(t)^4/\rho(t).
\tag{6}
\]

Let \(\psi_t(v)=\mathbb E_t e^{ivY}\), \(v\in[-\pi,\pi]\). In the sparse range \(t\ge1\), use independent \(Y,Y'\) and the two atoms \(0,1\) in \(1-|\psi_t(v)|^2=\mathbb E(1-\cos(v(Y-Y')))\) to obtain
\[
|\psi_t(v)|\le e^{-c\rho(t)\sin^2(v/2)}.
\tag{7}
\]
For the dense range \(0<t\le1\) we need two estimates:
\[
\sup_{0<t\le1}\sup_{\epsilon t\le |v|\le\pi} |\psi_t(v)|<1
\quad\text{for each }\epsilon>0,\qquad
\int_{-\pi}^{\pi}|\psi_t(v)|^{16}\,dv\le Ct .
\tag{8}
\]

To prove the first, compactness and the two atoms suffice when \(t\) is bounded below. Suppose otherwise \(t\to0\), \(|v|\ge\epsilon t\), and \(|\psi_t(v)|\to1\). Set \(N=\lfloor t^{-1/2}\rfloor,\ m_0=\lfloor N/2\rfloor\), and \(\omega=\psi_t(v)/|\psi_t(v)|\). Since all \(1\le j\le N\) have \(\Pr(X=j)\ge c/N\),
\[
\frac1N\sum_{j=1}^N|e^{ivj^2}-\omega|^2
\le C\,\mathbb E|e^{ivX^2}-\omega|^2=2C(1-|\psi_t(v)|)\to0 .
\]
For each integer \(1\le\ell\le m_0\), the averages \(m_0^{-1}\sum_{j=1}^{m_0}e^{iv(2\ell j+\ell^2)}\) therefore tend to \(1\), uniformly in \(\ell\), by Cauchy–Schwarz on the two translated intervals. Their magnitudes are \(|\sin(m_0\ell v)/(m_0\sin(\ell v))|\), with the continuous interpretation. For a sequence with magnitudes tending to \(1\), \(m_0\operatorname{dist}(\ell v,\pi\mathbb Z)\to0\): if the scaled distance diverges the ratio tends to zero, and if it tends to a finite nonzero \(b\) the limiting ratio is \(|\sin b|/b<1\). This conclusion is uniform over \(\ell\) because taking any violating subsequence would contradict it. By \(\ell=1\), \(v=\pi d+o(1/m_0)\) for an integer \(d\). Then \(\ell=m_0\) yields \(v=\pi d+o(1/m_0^2)\), since \(m_0(v-\pi d)=o(1)\). The untranslated value of the average at \(\ell=1\) tends to \((-1)^d\) along any subsequence of fixed parity, so \(d\) must be even eventually. As \(|v|\le\pi\), this forces \(|v|=o(t)\), the desired contradiction.

For the integral bound in (8), Jacobi's eight-square formula gives \(r_8(j)\le16\sum_{d\mid j}d^3\le16\zeta(3)j^3\) for \(j\ge1\), where \(r_8\) denotes the representation count. Hence \(\Pr_t(S_8=j)=r_8(j)e^{-tj}/\theta(t)^8\le C t\) since \(\theta(t)\asymp t^{-1/2}\); \(j=0\) has mass \(O(t^4)\). By Parseval, \((2\pi)^{-1}\int|\psi_t|^{16}=\sum_j\Pr_t(S_8=j)^2\le Ct\). This supplies the necessary factor of \(t\) in the outer Fourier integral; a uniform spectral gap by itself would not give a uniform relative local limit when \(t\) is very small.

For completeness, apply Fourier inversion and set \(u=v\sigma(t)\sqrt m\). On \(|u|\le c_0\sqrt{m\rho(t)}\), Taylor expansion of the centered characteristic function and its logarithm, with (6), gives
\[
m\log\mathbb E_t e^{iu(Y-r(t))/(\sigma(t)\sqrt m)}
=-u^2/2+\frac{\gamma_3(t)(iu)^3}{6\sqrt m}
+O\big(u^4/(m\rho(t))\big).
\]
The centered characteristic function is within distance \(u^2/(2m)\) of \(1\) by the second-moment Taylor bound, so the branch of the log is the one near \(1\). For \(c_0\) sufficiently small the remainder is at most \(u^2/4\) in absolute value. The cubic term is imaginary, and Taylor expansion of \(e^{iw}\) for real \(w\) has second-order error at most \(w^2/2\). Thus the integrated error in replacing the exponential by \(e^{-u^2/2}(1+\gamma_3(t)(iu)^3/(6\sqrt m))\) on this arc is \(O((m\rho(t))^{-1})\), bounded by an integral of \(C e^{-u^2/4}(u^4+u^6)/(m\rho(t))\). The Gaussian tails outside the arc are exponentially small in \(m\rho(t)\) with fixed polynomial factors. In the sparse regime the arc in \(v\) has width bounded below by a positive constant, and (7) bounds the normalized outer integral by \(C\sqrt{m\rho(t)}\,e^{-c m\rho(t)}\). In the dense regime this arc has width comparable to \(t\), and (8) bounds the normalized outer integral by \(C\sqrt m\,\eta^{m-16}\) for some \(\eta<1\). Inverting the Gaussian and cubic terms now gives (5).

## From local energies to full-coordinate total variation

Under \(P_t^{\otimes n}\), the law given \(\sum_iX_i^2=E\) is exactly \(U_{n,E}\): each shell point has probability proportional to \(e^{-tE}\). If \(S_k=\sum_{i=1}^k X_i^2\), the likelihood ratio of the marginal against the product law is
\[
R=\frac{p_{n-k,t}(E-S_k)}{p_{n,t}(E)}.
\tag{9}
\]
In particular, \(S_k\) is sufficient for this total variation comparison: the full marginal distance is \(\tfrac12\mathbb E_t|R-1|\). At matched precision \(n\rho(t)=M\) exactly. Let \(Z_k=(S_k-kr(t))/(\sigma(t)\sqrt k)\).

For \(a\) bounded away from \(0,1\), (5) gives, uniformly in \(S_k\),
\[
R=g_a(Z_k)+O(M^{-1/2}),\qquad
g_a(z)=(1-a)^{-1/2}\exp\big(-az^2/(2(1-a))\big).
\]
Berry–Esseen with (6) gives Kolmogorov error \(O((k\rho(t))^{-1/2})\) for \(Z_k\). The test function \(|g_a-1|\) is of bounded variation uniformly on such intervals in \(a\), so the expectation in (9) differs by \(O(M^{-1/2})\) from the Gaussian expectation. Since \(g_a(z)\varphi(z)\) is the density of \(N(0,1-a)\), this proves the claimed error bound. Comparing the two normal densities gives (1); it also gives continuity at \(0\) and \(1\). The original distance is nondecreasing in \(k\) for fixed \(n,E,t\) by marginalization. This extends (2) to sequences with \(a\to0\) or \(a\to1\), by comparison to any fixed intermediate fraction and then taking that fraction to the endpoint.

For small \(a\), the cubic term in (5) vanishes at the denominator's mean, and the numerator's argument is \(-\sqrt{a/(1-a)}\,Z_k\). Since \(|(y^3-3y)\varphi(y)|\le C|y|\), for \(a\le 1/2\) we have
\[
|R-g_a(Z_k)|
\le C\left(\sqrt{a/M}\,|Z_k|+M^{-1}\right).
\]
Its expectation is \(o(a)\) when \(aM\to\infty\). The quotient \((g_a(z)-1)/a\) tends to \((1-z^2)/2\) uniformly on compact sets as \(a\to0\), and its absolute value is bounded by \(C(1+z^2)\) for all \(z\) and \(0<a\le1/2\). The centered standardized fourth moment of \(Z_k\) is bounded by \(3+C/(k\rho(t))\) by expansion and (6), so this family is uniformly integrable. Berry–Esseen gives \(Z_k\Rightarrow N(0,1)\). Consequently the distance divided by \(a\) tends to \(\tfrac14\mathbb E|1-Z^2|=\varphi(1)\), by integrating the standard normal density over \(|Z|\le1\).

For fixed energy \(e>0\), the shell has \(2^e\binom ne\) points with all coordinates in \(\{0,\pm1\}\); any other point occupies at most \(e-3\) sites because an occupied magnitude at least two costs at least four units of energy. The latter points number \(O_e(n^{e-3})\) if \(e\ge4\) and are absent otherwise. Discarding them costs \(O_e(n^{-3})\) in TV. The remaining shell draws \(e\) distinct sites uniformly and gives each an independent fair sign. Under the matched product, \(q=e^{-t}\asymp e/n\) and replacing each \(X_i\) by an independent signed Bernoulli with occupation probability \(e/n\) costs \(O_e(n q^4)=O_e(n^{-3})\), because both the mass and the expected squared magnitude from \(|X_i|\ge2\) are \(O(q^4)\). In both models the absolute positions and signs in the first \(k\) sites have the same conditional distribution given their count. The counts are respectively hypergeometric and \(\operatorname{Bin}(k,e/n)\). Sampling the \(e\) sites with replacement changes the first count by at most \(O_e(1/n)\) by the collision probability, yielding \(\operatorname{Bin}(e,a)\). Comparing each independent Bernoulli \((e/n)\) with a Poisson \((e/n)\) at distance \(O_e(1/n^2)\) changes the second count by \(O_e(1/n)\), yielding \(\operatorname{Poi}(ae)\). This proves (3).

## Optimality over product Gaussian precisions

Let \(F(t)=\log\theta(t)\), so \(F'(t)=-r(t)\), \(F''(t)=\sigma(t)^2\), and \(|F'''(t)|=|\mathbb E_t(Y-r(t))^3|\). If \(|h_n|\) is bounded, then \(s_n-t=O((\sigma(t)\sqrt k)^{-1})\), which is \(O(t/\sqrt k)\) in the dense range and \(O((k\rho(t))^{-1/2})\) in the sparse range. In the segment from \(t\) to \(t+2(s_n-t)\), precision remains positive eventually and both \(\sigma(\cdot)/\sigma(t)\) and \(\rho(\cdot)/\rho(t)\) stay bounded above and below by positive constants. Taylor expansion and (6) then give the second likelihood ratio
\[
\log\frac{d P_{s_n}^{\otimes k}}{d P_t^{\otimes k}}
=-h_n Z_k-h_n^2/2+O((k\rho(t))^{-1/2}).
\]
The error is deterministic. The likelihood ratio has bounded second moment: apply the same Taylor expansion at precision \(t+2(s_n-t)\) and use that its likelihood ratio has expectation one. Thus the likelihood ratios are uniformly integrable. Comparing this density with (9) and using the Gaussian limit for \(Z_k\) proves (4), since \(e^{-hz-h^2/2}\varphi(z)\) is the density of \(N(-h,1)\). The same argument with bounded tests gives weak convergence of \(Z_k\) under each of the two laws to the respective normals.

If \(h_n\to+\infty\), compare \(P_{s_n}^{\otimes k}\) with precision \(t+H/(\sigma(t)\sqrt k)\) for any fixed \(H>0\). The block energy is stochastically decreasing in precision, since its likelihood ratio under increased precision is decreasing in the energy. Thus \(\Pr_{s_n}(Z_k\ge-A)\) is eventually bounded above in the limit by \(\Pr(N(-H,1)\ge-A)\). For fixed large \(A\), the shell probability of the same event tends to a value close to \(1\), and then \(H\) can be arbitrarily large. This proves distance tending to \(1\). The negative case is identical using the opposite tail and a decreased precision, which is positive for any fixed \(H\) eventually. The reasoning covers sequences with divergent \(|h_n|\) by subsequences.

Finally, for any two symmetric unimodal densities, translating one relative to the other cannot increase their overlap integral \(\int\min(f,g)\): by the layer-cake formula the superlevel sets are intervals, and their intersection at each level has largest length when centers coincide. For the distinct centered normals here the improvement is strict for any nonzero translation: at the common positive crossing \(z_a\) of their densities both level radii are equal and nonzero, so the intersections shorten at that level and on an interval of nearby levels. This proves the optimality and uniqueness in the scaled precision variable by applying (4) on subsequences, and by excluding divergent \(|h_n|\).

## Prior work and scope

[Diaconis–Freedman, *Conditional limit theorems for exponential families and finite versions of de Finetti's theorem*](https://doi.org/10.1007/BF01048727), especially [the original report, (1.8)–(1.14)](https://digicoll.lib.berkeley.edu/record/86140), gives the general conditional Gaussian profile and the small-fraction first-order mechanism under regularity conditions in the continuous setting. The shell conditioning identity and the resulting normal profile at a fixed regular parameter are not claimed new. The result here verifies a single uniform discrete local estimate spanning arbitrarily high energy, vanishing energy per site with diverging total energy, and the normal-to-bounded-energy change of limit. In the sparse range the standardized fourth moment is unbounded, while in the high-energy range the Fourier integral needs a precision-dependent prefactor. The elementary quadratic phase argument and the eight-square count supply that prefactor and a uniform frequency gap without a growth restriction on \(E\). For the classical eight-square identity see [Cooper and Hirschhorn, equation (2.10)](https://web.maths.unsw.edu.au/~mikeh/webpapers/paper139.pdf).

This is a distributional comparison for a toy energy constraint, not an algorithm or a result about a concrete cryptographic system. The accompanying replay checks exact finite shell identities and generated numerical examples, not the proof itself.

Replay with `node verify-discrete-gaussian-energy-shells.js`. The last run passed 67,682 exact and 35,236 numerical checks.
