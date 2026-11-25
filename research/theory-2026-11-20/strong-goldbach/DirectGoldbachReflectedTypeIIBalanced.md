# Balanced cancellation in the reflected Goldbach Type II sum

Assume Dirichlet GRH. Choose the Vaughan cutoffs \(U=X^{1/8}\), \(V_0=X^{1/1000}\), with integer rounding. In the [true reflected Type II sum](DirectGoldbachReflectedMobiusTypeI.md), the contribution of \(a,b,d,e\asymp\sqrt X\) is \(O_\epsilon(X^{999/1000+\epsilon})\), for each fixed even \(X=N\). The same conclusion holds in any prescribed fixed-power logarithmic neighborhood of these scales. It does not control the full Type II sum.

Keep the weight and coprimality conditions of the linked decomposition, and set \(\kappa=\sigma=1/1000\), \(R=\sqrt X\). Open \(\beta(b)=\log b-\sum_{\ell\mid b,\ \ell\le V_0}\Lambda(\ell)\), with the log term indexed by \(\ell=1\). Open \(\mu^2(d),1_{(d,e)=1},1_{(d,N)=1}\) by the divisor variables \(k^2\mid d,\ j\mid(d,e),\ r\mid(d,N)\), respectively. Truncate \(k,j,r\le X^\kappa\). For the \(k,j\) tails count \(de\le X\) divisible by \(k^2,j^2\), respectively, and for the \(r\) tail count those divisible by \(r\mid N\). For a given \(de\), the factorizations on either side and all remaining weights, even after the divisor expansions, cost \(X^\epsilon\). Summing the inverse squares and using \(\tau(N)\ll_\epsilon X^\epsilon\) costs \(O(X^{1-\kappa+\epsilon})\). This tail estimate may be made before opening \(\beta\), or after it by using \(\sum_{\ell\mid b}\Lambda(\ell)=\log b\).

Smooth all sharp box edges and the inequalities \(e>d\) and \(d\le D_0\), when present, in relative width \(X^{-\sigma}\). The error is \(O(X^{1-\sigma+\epsilon})\): in each boundary strip count the pairs \((d,e)\) when the edge is in those variables or \(e-d\), and \((a,b)\) otherwise; the opposite factorization count and all weights cost \(X^\epsilon\). The inequalities \(a>U,\ b>V_0\) are automatic in these boxes. Work on one pair of dyadic scales for each variable; fixed logarithmic departures from \(R\) are covered by polylogarithmically many such boxes. In the following \(X^\epsilon\) allowances absorb any fixed logarithmic factors.

For fixed \(k,j,r,\ell\) put \(H=[k^2,j,r]\), \(m=He,\ n=\ell a\), \(d=Ht,\ b=\ell v\). The equation is \(mt+nv=N\). Write \(w(a,e,x)\) for the smooth weight evaluated at \(x=de\), \(d=x/e,\ b=(N-x)/a\); it includes \(\log(e/d)\) and, for the log term, \(\log b\). It is supported on an \(x\) interval of length \(O(X)\); normalized derivatives in \(a,e,x\) of total order \(i\) cost \(O_i(X^{i\sigma+\epsilon})\). The factor \(1_{j\mid e}\) stays in the coefficient of \(\mu(e)\).

For \(g=(m,n)\) a solution requires \(g\mid N\). Writing \(m'=m/g,\ n'=n/g\), one has \(t\equiv (N/g)\overline{m'}\pmod{n'}\); thus \(x\) runs in an arithmetic progression of step \(mn/g\). Poisson in \(x\), with \(e(z)=\exp(2\pi iz)\), gives terms
\[
 \frac{g}{mn}\int_{\mathbb R}w(a,e,x)
  e\!\left(\frac{h(N/g)\overline{m'}}{n'}-\frac{hgx}{mn}\right)\,dx,\quad h\in\mathbb Z .
\]

For \(h=0\), open \((m',n')=1\) using \(s\) dividing both, so \(a\) is a multiple of \(u=gs/(gs,\ell)\) and \(e\) a multiple of \(v_1=gs/(gs,H)\). For fixed \(e,x\), RH for \(\mu\) on multiples of \(u\) with the induced coprimality and partial summation give \(O_\epsilon(X^{\sigma+\epsilon}\sqrt{R/u})\), after normalizing the factor \(1/a\) by \(1/R\). Indeed, when \(\mu(u)\ne0\), writing \(a=uy\) yields \(\mu(u)\mu(y)1_{(u,y)=1}\), to which the [prefix bound](DirectGoldbachReflectedMobiusTypeI.md) applies. There are \(O(R/v_1)\) choices of \(e\) whenever the scale supports any. Integrating \(x\) and including the prefactor bounds the zero mode by
\[
 \ll_\epsilon X^{\sigma+\epsilon}
 \sum_{g\mid N}\sum_{s\ge1}\frac{g}{H\ell}
       \frac{R}{v_1}\sqrt{\frac{R}{u}}
 \ll_\epsilon X^{3/4+\sigma+\epsilon},
\]
using \(v_1\ge gs/H,\ u\ge gs/\ell\) and summability of \(s^{-3/2}\).

For \(h\ne0\), integrate by parts to restrict to \(|h|\le (H\ell/g)X^{\sigma+\epsilon'}\), with arbitrary fixed \(\epsilon'>0\) and arbitrarily small remaining error by increasing the derivative count. For each \(x,g,h\) the first phase is precisely a bilinear Kloosterman fraction; apply [Bettin–Chandee, Theorem 1](https://arxiv.org/pdf/1502.00769) with its summation variable supported at 1, scales \(M\asymp HR/g,\ Q\asymp\ell R/g\), and parameter \(hN/g\). The two coefficient norms have product \(\ll R X^\epsilon\), as \(a\mapsto n'\) and \(e\mapsto m'\) are injective on the surviving integers. The factor \(1+|h|N/(gMQ)\) is \(O(X^{\sigma+O(\epsilon')})\). The smooth factors in the integral may depend on both \(a,e\): two-dimensional Abel summation, including the second phase and normalized \(1/(ae)\), costs at most \(X^{2\sigma+O(\epsilon')}\). This follows from the normalized derivative bounds and \(|hgx/(mn)|\ll X^{\sigma+O(\epsilon')}\). The theorem's second bracket term (the term of exponent \(3/8\) in \(MQ\)) is bounded by the first for \(M,Q\) bounded below by an absolute positive constant, since \((MQ)^{1/40}\ll(M+Q)^{1/8}\). Outer boxes with nonempty integer support have scales bounded below in this sense.

The integral and prefactor cost \(O(g/(H\ell))\) up to log factors, and summing the frequency count cancels this factor and costs \(X^{\sigma+O(\epsilon')}\). Bounding the remaining powers of \(M,Q\) with \(g\ge1\) yields an error for each auxiliary tuple
\[
 \ll_\epsilon X^{39/40+(7/2)\sigma+\epsilon}
 (H\ell)^{7/20}\max(H,\ell)^{1/4}.
\]
Here \(\tau(N)\) from summing \(g\mid N\) is absorbed into epsilon. Since \(H\le X^{4\kappa},\ \ell\le X^\kappa\), and at most \(X^{4\kappa}\) tuples are summed, the aggregate exponent is at most \(39/40+(7/2)\sigma+(27/4)\kappa=0.98525\), up to epsilon. The zero mode remains smaller as well. Truncation and smoothing dominate with exponent \(999/1000\), as asserted.

The earlier Type I argument is still valid: it only requires the short cutoffs \(V_0\) and \(UV_0\) to be small enough. Neither the present bound nor the earlier short-factor bound controls, for example, scales \((d,e,a,b)=(X^{1/4},X^{3/4},X^{3/5},X^{2/5})\); beyond balanced boxes the \(\ell^2\) bound on the outer coefficients no longer suffices. This proof does not establish positivity at any fixed target on its own.
