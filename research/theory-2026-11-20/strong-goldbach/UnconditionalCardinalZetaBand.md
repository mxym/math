# Unconditional cardinal-band identity and a strictly positive rational part

This companion removes all Riemann hypotheses for the **fixed** compact positive-ordinate zeta band of [CardinalPositiveZetaBand.md](CardinalPositiveZetaBand.md). Zeros now have their actual real parts. The unconditional rational cutoff here is \((\log X)^C\) for fixed \(C\), not a fixed power of \(X\). Its true signed contribution is positive for every sufficiently large even target if \(C\) is large. Its relative difference from the full Hardy–Littlewood main is uniformly \(O(e^{-C})+o_C(1)\), instead of the absolute \(o(X)\) error from the full singular series obtained conditionally with polynomial cutoff. No sign bound for the remaining minor part is proved.

Retain the canonical positive band \(I\), \(P_u=G/A_u\), the compact-ratio weight \(w\), the even target \(N\), \(X=N-1/2,\ H=X^{2/5},\ \delta=1/X,\ L=\log X\), and the geometric set \(\mathcal B_X\) as in the linked note. For actual zeta zeros \(\rho=\beta+i\gamma,\rho'=\beta'+i\gamma'\), with multiplicity and \(t=\gamma+\gamma'\), set
\[
 B_*(\rho,\rho')=X^{1+\rho+\rho'}c(\rho)c(\rho')
       \int w(u)u^\rho(1-u)^{\rho'}P_u(t/X)du .
\]
There is no RH normalization hidden in this expression. Unconditionally
\[
 R_w(N)=\sum_{\mathcal B_X} B_*(\rho,\rho')+o(X).                             \tag{1}
\]
For fixed \(C\ge1,\ Q=\lfloor L^C\rfloor\), form exactly the mask \(M_X\) of the linked note with this \(Q\): denominators \(q\le Q\) and \(2d\) for odd \(d\le Q\), distinct reduced rationals in \([-1,1]\). For every fixed \(A>0\),
\[
 \sum_{\mathcal B_X}B_* M_X(t)
   = X\left(\int w\right)\mathfrak S_Q^*(N)+O_{A,C,w,F,G}(X L^{-A}),
 \quad \mathfrak S_Q^*(N)=
   2\!\!\sum_{\substack{d\le Q\\d\ {\rm odd}}}\frac{\mu(d)^2c_d(N)}{\varphi(d)^2}. \tag{2}
\]
The sum over actual zeta pairs is complex and has the stated *real* main; the implied constants may be ineffective. Uniformly for sufficiently large even \(N\),
\[
 |\mathfrak S_Q^*(N)-\mathfrak S(N)|\ll e^{-C}\mathfrak S(N)                 \tag{3}
\]
with an absolute implied constant independent of \(C\) (enlarging it handles the floor). In particular for fixed large \(C\) (2) is a positive signed estimate of order \(X\mathfrak S(N)\) in real part. The exact unestimated term for \(R_w(N)\) is \(\sum_{\mathcal B_X}B_*[1-M_X(t)]\) up to the stated errors. A positive selection of pairs is not positivity of the whole.

## 1. Off-line spectral transfer

We give the details simultaneously for the compact symbol \(D_u(\lambda)=P_u(\lambda)\) and for each \(D_u(\lambda)=P_u(\lambda)F(H(\lambda-\tau))\) in the mask. Write \(H_0=1\) in the first case and \(H_0=H\) in the second. The inverse transform \(k_u(s)\) is \(b_u(s)\) or the convolution in (6) of the cardinal note. For each fixed \(j,B\),
\[
 |\partial_u^j k_u(s)|\ll_{j,B} H_0^{-1}(1+|s|/H_0)^{-B},
 \qquad \|\partial_u^j\partial_\lambda^n D_u\|_\infty\ll_{j,n}H_0^n.          \tag{4}
\]
All \(\lambda\)-derivatives remain supported in the same fixed compact subset of \(I\). Use (4) of the cardinal note for this kernel, truncating smoothly to \(|s|\le 2H_0 X^{1/200}\).

The usual zeta explicit formula for \(U_\delta\) has the same pole/trivial-zero terms and symmetric cutoff interpretation as in the reflected shell note, without RH. In a fixed compact \(y/X\)-window the squared \(L^2(dy)\)-norm of a dyadic block \(T<|\gamma|\le2T\) is now at most
\[
 \ll X^3\min(\delta^2 T,T^{-1})\log^2(2T).
\]
Indeed after scaling \(y=Xu\), the amplitude contains \(u^{\beta+\beta'}\) with uniformly bounded derivatives of every fixed order; the exterior \(X^{1+\beta+\beta'}\le X^3\). The same Fourier decay in ordinates and local row-sum bound apply. Thus removing all \(|\gamma|>X^4\) costs \(O(X^{-1/2}L)\) in local norm. The norm of the **full** zero sum is \(O(\sqrt{XL})\) from the exact arithmetic increment, whose integer cells are disjoint here, not from a pointwise bound for the zeros. The error of truncating both factors in the reflected product is \(O(L^2)\) after integrating (4). Unlike the RH proof, no lower height cutoff is made at this stage.

In each finite pair term the real-part correction \(e^{(\beta+\beta'-1)s/X}\) remains after multiplying the moving scale by \(e^{-2s/X}\). Its Taylor terms through order \(K=24\) yield the multipliers
\[
 \frac{(\beta+\beta'-1)^m}{m!(iX)^m}\partial_\lambda^m D_u(\lambda),
 \qquad \lambda=t/X,\quad 0\le m\le K.
\]
The cutoff on each Fourier integral is negligible to arbitrary powers by (4), including the moments used. The remainder per term is \(O((H_0 X^{1/200}/X)^{K+1})\) before its exterior prefactor, uniformly also after fixed \(u\)-derivatives. There are \(O(X^8L^2)\) cutoff pairs and \(X^{1+\beta+\beta'}|c c'|\ll X\); hence the cumulative remainder tends to zero by a power. The same Taylor argument for pole/pole gives zero at every retained Taylor order because all derivatives of \(D_u\) vanish at zero. For a pole/zero term the amplitude has one ordinate \(\gamma\) and a bounded real-part shift (the residual factor is \(e^{\beta s/X}\)); all Taylor multipliers vanish unless \(\gamma/X\in I\). There the \(u\) phase has derivative \(\asymp X\) of fixed sign, so repeated integration by parts beats all polynomial prefactors and derivative costs. Smooth trivial-zero errors remain negligible.

For the pair terms at each Taylor order, outside \(\mathcal B_X\) the nonstationary \(u\)-integrations of the cardinal note likewise beat every required power (derivatives of \(u^\beta(1-u)^{\beta'}\) are uniformly bounded). Inside \(\mathcal B_X\), \(\gamma,\gamma'\asymp X\) and the phase second derivative is \(-\gamma/u^2-\gamma'/(1-u)^2\), uniformly of magnitude \(\gg X\) with fixed sign. The second-derivative van der Corput integral bound gives
\[
 \left|\int w\,u^\rho(1-u)^{\rho'}\partial_\lambda^m D_u(\lambda)\,du\right|
   \ll_m X^{-1/2}H_0^m.
\]
The classical unconditional [Ingham density theorem (see Chourasiya–Simonič, v2, Corollary 1 for the uniform form at the left endpoint)](https://arxiv.org/html/2507.15184v2) gives, for \(1/2\le\sigma\le1\),
\(N(\sigma,T)\ll T^{3(1-\sigma)/(2-\sigma)}(\log(2T))^{O(1)}\).
Consequently
\[
 \sum_{cX\le\gamma\le C'X} X^\beta \ll X^{3/2}L^{O(1)}.
\]
For \(\beta<1/2\) use the ordinary zero count. On the other side integrate \(L X^\sigma N(\sigma,C'X)\,d\sigma\); the exponent \(\sigma+3(1-\sigma)/(2-\sigma)\) is at most \(3/2\) on the stated interval. Since \(|cc'|\ll X^{-2}\) here, the total absolute contribution of each \(m\ge1\) Taylor term is
\[
 \ll_m X^{-3/2}(H_0/X)^m
       \left(\sum_{\gamma\asymp X} X^\beta\right)^2
 \ll_m X^{3/2}(H_0/X)^m L^{O(1)} .
\]
For \(H_0=H=X^{.4}\) this is \(O(X^{.9}L^{O(1)})\), and it is smaller for \(H_0=1\). The \(m=0\) term is exactly the required \(B_*\) sum, with \(F\) in the masked case. This proves uniform spectral transfer at error \(O(X^{.91})\) for large \(X\), more than enough even after summing log-power many centers. The arithmetic cardinal sampling argument (5) of the companion used no RH. Its geometric and proper-power errors there are power saving, proving (1).

## 2. Unconditional moving progression phases at logarithmic denominators

Only the short progression input in estimating the rational *arithmetic* averages must be replaced. We use [Koukoulopoulos, Primes in short arithmetic progressions, Theorem 1.2](https://dms.umontreal.ca/~koukoulo/documents/publications/shortaps.pdf), not a hypothesis on zeros. In its range \(h'=x^\theta,\ 1/6+2\epsilon\le\theta\le1/2,\ Q'^2\le h'/x^{1/6+\epsilon}\), the theorem estimates \(\int_x^{2x}\sum_{q\le Q'}E(y,h';q)\,dy\ll_{\epsilon,B} xh'(\log x)^{-B}\) for every fixed \(B\), where \(E\) is the maximum absolute log-prime discrepancy over unit residue classes. Its whole range easily includes \(X^{.30}\le h'\le X^{.405}\) and all \(q\le 2L^C\), with room in both exponents, for \(x\asymp X\). A finite dyadic cover treats fixed compact \(y/X\)-windows.

For any fixed Schwartz \(f\) of mass one, the continuous \(m\)-mean absolute error in
\[
 \sum_{p'}(\log p')e(-a p'/q) f((p'-m)/H)
       \quad\hbox{versus}\quad H\mu(q)/\varphi(q)
\]
is \(O_{A,C}(X H L^{-A})\) throughout the central \(m\) interval for every \(A\). Indeed express the smooth error in each unit class by integrating the errors of positive and negative one-sided intervals of lengths \(H|v|\) against \(f'(v)\), by partial summation. For \(X^{-.10}\le |v|\le X^{1/200}\) use Theorem 1.2 as above, shifting the base by \(H|v|\) when needed; the shifted \(m\)-window stays inside a fixed compact multiple of \(X\). For smaller \(v\) the trivial \(O((H|v|+1)L)\) per interval gives a power saving after integration, and larger \(v\) are killed by Schwartz decay (allow the trivial bound polynomial in \(X,H,|v|\)). Summing over at most \(q\) unit classes and treating \(p'\mid q\) separately costs only log powers. Sum absolute errors over the half-integer mesh as well: moving \(m\) by at most one changes the smooth sum by \(O_f(L)\) on this range using its bounded rapidly decreasing derivative. This adds \(O(XL)\) to the previous bound. The principal density term is independent of the center. On the mesh \(m=X-p\) one can now bound \(\log p\) by \(L\) and enlarge the nonnegative absolute-error sum to the whole mesh. After division by \(H\) this costs \(O_{A,C}(X L^{-A})\), with a freely larger log exponent chosen in the input. The long outer smooth prime sum in the same additive phase uses ordinary Siegel–Walfisz and partial summation, since \(q\le 2L^C\); all outer test weights have uniformly bounded total variation. These uses of small moduli need no power-saving constant or effectivity.

The cardinal/rational multiplier convolution, its integrated \(O(XL^2/H)\) freezing error on the arithmetic side, the aperture phase on each cell, and the logarithmic-delay curvature errors are exactly those proved arithmetically in the two companions and do not depend on RH. Use the **unconditional spectral transfer** of §1 with the unfrozen product symbol, then (6) of the cardinal note on the arithmetic side to freeze \(P_u(2\pi r)\), then the just-proved unconditional short and long prime estimates. There are at most \(O_C(L^{2C})\) rational centers, and all errors can therefore be made \(O_{A,C}(XL^{-A})\) in total. Pairing the \(d\) and \(2d\) fractions for odd squarefree \(d\) as in the cardinal note gives precisely (2).

## 3. Uniform relative singular-series tail

For even \(N\), \(g(d)=|\mu(d)^2 c_d(N)|/\varphi(d)^2\) is multiplicative on squarefree \(d\), with \(g(p)=1/(p-1)\) for \(p\mid N\) and \(g(p)=1/(p-1)^2\) otherwise. Its full absolute Euler product is at most an absolute constant times \(\mathfrak S(N)\): the two products have identical local factors at \(p\mid N\), and the product of ratios \((1+(p-1)^{-2})/(1-(p-1)^{-2})\) for \(p>2\) converges. Put \(v=1/\log\log X\). For all large \(X\),
\[
 \sum_d g(d)d^v\ll\sum_d g(d).
\]
For \(p\nmid N\) the change in the log Euler product is \(O(1)\) by absolute convergence at exponent \(v\le1/4\). For \(p\mid N,\ p\le L^2\), \(p^v-1\ll v\log p\) uniformly there, and \(\sum_{p\le L^2}\log p/p\ll\log L\). Larger prime divisors are at most \(O(L/\log L)\) in number; each contributes \(O(L^{-2+2v})\), so together \(o(1)\). Rankin's bound now gives \(\sum_{d>Q} g(d)\ll Q^{-v}\mathfrak S(N)\). Restricting to odd \(d\), doubling, and allowing the floor proves (3). A single fixed \(C\) is not claimed to give absolute \(o(1)\) tail for all very composite targets. For any desired fixed relative tolerance choose \(C\) first, then \(N\) sufficiently large. All bounds concern the real primes and actual zeta zeros, but do not control the signed minor aggregate.

The relevant historical explicit-formula and circle-method antecedents are credited in [the reflected shell note](ReflectedZetaMajorMinorShells.md) and its companions. No novelty is claimed for the density estimate, short-AP theorem, singular series, or elementary sampling and Rankin inequalities.
