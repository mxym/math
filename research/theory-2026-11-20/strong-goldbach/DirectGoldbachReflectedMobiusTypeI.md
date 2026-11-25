# Type I cancellation in the genuine reflected Möbius term

Under Dirichlet GRH, the two Type I terms of Vaughan's identity are power-small in the **true parity-twisted sum** of the [squarefree complementary-divisor splitting](DirectGoldbachComplementaryMobiusHalf.md), for every fixed large even target. This includes the entire complementary range \(d<e\), not only \(d\le \sqrt X/\log^B X\). The Type II contribution remains unestimated.

Put \(X=N\). Let \(V\) be a fixed smooth test compactly supported in \((0,1)\), and keep an optional upper cutoff \(d\le D_0\le\sqrt X\). In the parity-twisted half of the exact identity, after multiplying by \(\mu^2(N-p)\), write \(m=de\). For squarefree \(m\), \(\mu(d)\mu(de)=\mu(e)\); conversely \(\mu^2(d)\mu(e)\mathbf1_{(d,e)=1}\) imposes squarefreeness of \(de\) whenever the summand is nonzero. The sum to estimate is therefore
\[
 \sum_{\substack{d\le D_0\\ (d,N)=1}}\mu^2(d)
 \sum_{\substack{e>d\\(e,d)=1\\ X-de\ {\rm prime}}}
 \log(X-de)\,\mu(e)\,V(1-de/X)\log(e/d).
\]
The restriction \((d,N)=1\) loses nothing because on the support \(p=X-de\asymp X>d\). Replace the prime log-weight by \(\Lambda(X-de)\), keeping \((d,N)=1\). The extra proper powers cost \(O_\epsilon(X^{1/2+\epsilon})\), from the \(O(\sqrt X\log X)\) possible proper powers, the divisor count of \(X-p\) and log weights. This substitution is made before splitting \(\Lambda\).

## Möbius in a genuine progression

Fix \(\epsilon>0\). On Dirichlet GRH the twisted Möbius prefix satisfies
\[
 \sum_{n\le y}\mu(n)\chi(n)\ll_{\epsilon,C} y^{1/2+\epsilon} X^\epsilon
 \quad (1\le y\le X,\ {\rm modulus}\ \le X^C).
\]
Here \(X\) is an ambient parameter and \(C\) is any fixed constant. To obtain the uniform version, use the GRH Littlewood bound \(1/L(\sigma+it,\chi)\ll_{\epsilon,\eta}(q(2+|t|))^\eta\) for \(\sigma\ge1/2+\epsilon/2\), with fixed arbitrarily small \(\eta\), on the reciprocal Dirichlet series. For completeness, the Littlewood bound follows by taking a zero-free branch of the logarithm on the right of \(1/2\), applying Borel–Carathéodory on disks centered at \(2+it\) and lying in this half-plane, and using polynomial bounds for \(L\) there. This gives \(|\log L|\ll_\epsilon\log(q(2+|t|))\) on \(\sigma\ge1/2+\epsilon/4\). On the right line \(\sigma=1+\epsilon\) the Euler logarithm is bounded. Applying three lines to the logarithm times \(\exp((s-it_0)^2)\) interpolates the bound at a fixed height \(t_0\) to a strict power of \(\log(q(2+|t_0|))\) at \(\sigma\ge1/2+\epsilon/2\); exponentiation gives every prescribed conductor-height power. For the principal factor use \((s-1)\zeta(s)/(s+1)\) in the logarithm and then restore the reciprocal factor. For an induced character the extra Euler factors on this line only cost \(q^{o(1)}\). Truncated Perron at a half-integer cutoff and height \(X^J\), for a fixed sufficiently large \(J\), then shifts to \(1/2+\epsilon/2\). The horizontal terms and the truncation error are negligible, and the vertical integral costs \(y^{1/2+\epsilon/2} X^{O_{C,J}(\eta)}\log X\), proving the claimed bound. A sharp lower cutoff is therefore allowed as well.

For a fixed \(d\) and a coefficient \(k\) in a Vaughan Type I convolution, impose \(k\mid X-de\). If \((d,k)>1\), there are no solutions because \((d,N)=1\). Otherwise \(e\equiv a\bmod k\), where \(a\equiv N\bar d\bmod k\). Put \(g=(a,k)=(N,k)\). If \(g\) is not squarefree, the Möbius term vanishes. Otherwise put \(e=gn\). The resulting single progression for \(n\) modulo \(k/g\) is reduced, and the Möbius weight becomes \(\mu(g)\mu(n)\mathbf1_{(n,g)=1}\). Impose also \((n,d)=1\), since \((g,d)=1\). Orthogonality on the reduced progression, multiplying by the coprimality indicator modulo \(gd\), acts through (possibly imprimitive) characters modulo \([k/g,gd]\), bounded by a fixed power of \(X\). The \(1/\varphi(k/g)\) normalization cancels the character count when using the prefix bound. For \(d\asymp H\) the length scale for \(e\) is \(X/H\), so partial summation yields \(O_\epsilon((X/H)^{1/2}X^\epsilon)\), after shrinking the epsilon used above, with either Type I inner weight \(1\) or \(\log((X-de)/k)\), and with the common factors \(V(1-de/X)\log(e/d)\). On the physical support the weights and their total variations cost at most a fixed power of \(\log X\). The sharp endpoint \(e>d\) adds no loss.

## What Vaughan leaves

Use \(\Lambda=\mu_{\le U}*\log-\mu_{\le U}*\Lambda_{\le V_0}*1+\Lambda_{\le V_0}+\mu_{>U}*\Lambda_{>V_0}*1\), where \(V_0\) is a numeric Vaughan cutoff, not the smooth test \(V\). The short prime term vanishes on the support. The other two Type I terms have \(k\le K=UV_0\) with divisor-bounded coefficients, so their contribution on a \(d\)-dyad \(d\asymp H\) is
\[
 O_\epsilon(X^{1/2+\epsilon}H^{1/2}K).
\]
In particular take \(U=V_0=X^{1/8-\delta}\), any fixed \(0<\delta<1/8\). Summing the dyads up to \(H\le\sqrt X\) gives a power saving \(O_\delta(X^{1-\delta})\) after choosing the internal epsilon small. This uniform proof applies for every \(D_0\) as above, including the whole parity-twisted divisor sum.

The exact remaining term is supported on \(de+ab=N\), \(a>U,\ b> V_0\), \(e>d\), with coefficients \(\mu^2(d)\mu(e)\mu(a)\sum_{\ell\mid b,\ \ell>V_0}\Lambda(\ell)\), coprimality conditions as above, and the indicated test and log ratio. The proof has not bounded its sign or its size below the positive untwisted main term. The separate untwisted log-wide strip can also still contribute at the main scale.
