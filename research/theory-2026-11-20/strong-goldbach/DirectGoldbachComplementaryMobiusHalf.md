# The short complementary-divisor term on actual squarefree complements

There is a genuine fixed-target main term on the untwisted side of an exact Möbius splitting. This uses RH for the ordinary Möbius summatory bound and unconditional Bombieri–Vinogradov for primes. It neither estimates the parity-twisted term nor proves a positive prime-pair count.

Let \(X=N\) be large and even, let \(w,g\) be fixed smooth nonnegative tests compactly supported inside \((0,1)\), and write \(V(u)=w(u)g(1-u)\), \(I=\int V(u)\,du\). In all sums put \(m=N-p\). For squarefree \(m>1\) set
\[
 H(m)=\sum_{\substack{d\mid m\\d<\sqrt m}}\mu(d)\log(m/d^2).
\]
Complementary divisors in \(\sum_{d\mid m}\mu(d)\log(m/d)=\Lambda(m)\) give the exact identity
\[
 \Lambda(m)=\tfrac12(1-\mu(m))H(m).
\]
To see the coefficient, use \(\log(m/d)=\tfrac12\log m+\tfrac12\log(m/d^2)\), \(\sum_{d\mid m}\mu(d)=0\), and \(\mu(m/d)=\mu(m)\mu(d)\) on squarefree \(m\). In particular the parity factor is not optional.

For every fixed \(A>0\), choose a sufficiently large fixed \(B=B(A)\) and take \(D=\sqrt X/(\log X)^B\). Let \(H_D(m)=\sum_{d\le D,d\mid m}\mu(d)\log(m/d^2)\), defined on all \(m\). Then uniformly in even \(N\),
\[
 \sum_p \log p\,V(p/X)\mu^2(N-p)H_D(N-p)
 =2X\mathfrak S(N)I+O_A(X/\log^A X).
\]
On the support all \(d\le D\) are genuinely below \(\sqrt m\), so this is a component of the exact squarefree identity.

## Opening the squarefree condition

Expand \(\mu^2(m)=\sum_{k^2\mid m}\mu(k)\) and truncate at \(K=(\log X)^J\) for a large fixed \(J=J(A)\). Uniformly \(|H_D(m)|\ll \tau(m)\log X\). Summing over integers rather than primes and applying \(\tau(k^2l)\le\tau(k^2)\tau(l)\) shows that the absolute truncation error is
\[
 \ll X(\log X)^3\sum_{k>K}\frac{\tau(k^2)}{k^2}
 \ll X(\log X)^3\frac{(\log(2K))^2}{K}.
\]
The last inequality follows from \(\tau(k^2)\le d_3(k)\) and the elementary threefold divisor moment. It is negligible at the requested precision for large \(J\).

For remaining \(d,k\), the modulus is \(q=[d,k^2]\le \sqrt X/(\log X)^{B-2J}\), hence below the Bombieri–Vinogradov range with any fixed logarithmic margin. If \((N,q)>1\) no supported prime can occur because \(p\asymp X>q\). Otherwise replace the weighted prime count by the continuous integral divided by \(\varphi(q)\). The test \(V(y/X)\log((N-y)/d^2)\) costs \(O(\log X)\) in partial summation, uniformly in \(d\). The maximal reduced residue errors can be summed with a divisor multiplicity: nonzero \(\mu(d)\mu(k)\) requires squarefree \(d,k\), so \(q\) determines \(k\) by its squared prime factors and leaves at most \(\tau(q)\) choices for \(d\). In detail write \(E(q)\) for the standard maximal prime-only progression error for prefixes up to \(X\). Ordinary BV gives the required logarithmic saving for \(\sum_q E(q)\) after making \(B-2J\) large enough. Passage from von Mangoldt to genuine primes costs at most the number of moduli times \(O(\sqrt X\log^2 X)\), also negligible on choosing \(B-2J\) accordingly. Also \(E(q)\ll X\log X/q\) in this range by counting integers, so \(\sum\tau^2(q)E(q)\ll X\log^C X\) by the elementary divisor moments. Cauchy–Schwarz and the resulting logarithmic saving pay both the \(\tau(q)\) weight and the extra log.

## Main coefficients

For every retained squarefree \(k\) coprime to \(N\), define
\[
 F_{N,k}(s)=\sum_{\substack{d\ge1\\(d,N)=1}}
       \frac{\mu(d)d^{-s}}{\varphi([d,k^2])}
 =\frac1{\varphi(k^2)}
   \prod_{\ell\mid k}(1-\ell^{-s})
   \prod_{\ell\nmid Nk}\left(1-\frac{\ell^{-s}}{\ell-1}\right)
 =\frac{G_{N,k}(s)}{\zeta(1+s)}
\]
initially for \(\Re s>0\), where \(\ell\) runs over primes. For fixed \(0<\eta<1/2\), the Dirichlet coefficients \(g(e)\) of \(G_{N,k}\) satisfy
\[
 \sum_e |g(e)|e^\eta
 \ll_\eta \varphi(k^2)^{-1}N^{o(1)} k^{\eta+o(1)}.
\]
Indeed the local ratio for \(\ell\nmid Nk\) is \(1+O(\ell^{-2+\eta})\) in absolute weighted coefficient norm, since numerator and denominator differ there by \((1/(\ell-1)-1/\ell)\ell^{-s}\). For \(\ell\mid N\) the factor is \((1-\ell^{-1-s})^{-1}\), the product of whose norms is \(N^{o(1)}\) uniformly (split the primes at any large fixed cutoff). For \(\ell\mid k\) the factor is \((1-\ell^{-s})/(1-\ell^{-1-s})\); its norm is at most \((1+\ell^\eta)/(1-\ell^{-1+\eta})\), giving \(k^{\eta+o(1)}\) by the same split. The resulting bounds sum over \(k\) absolutely, apart from \(N^{o(1)}\).

Under RH the classical \(M(x)\ll_\epsilon x^{1/2+\epsilon}\) bound and partial summation show that the tails beyond \(d>D\) for \(F_{N,k}(0)\) and \(F'_{N,k}(0)\), interpreted as their convergent coefficient sums, are at most \(O(D^{-\eta}(1+\log D)\sum_e|g(e)|e^\eta)\) after choosing \(\epsilon\) with \(\eta<1/2-\epsilon\). To check the derivative, convolve with \(\mu(n)/n\); if \(e\le D\) the weighted \(n>D/e\) tail is bounded by \(O((D/e)^{-\eta}(1+\log D))\) after partial summation, with a strict exponent to spare. For \(e>D\), bound the full \(n\)-sums, and absorb \(\log e\) by using the displayed weighted norm at a slightly larger exponent \(\eta'<1/2\). This also justifies agreement with the value and derivative of the analytic product near zero.

The zeta reciprocal has a simple zero at zero in this parametrization. Hence \(F_{N,k}(0)=0\) for every \(k\), and \(F'_{N,k}(0)=0\) whenever \(k>1\) because at least one numerator \(1-\ell^{-s}\) also vanishes. For \(k=1\),
\[
 F_{N,1}'(0)=G_{N,1}(0)
 = 2\prod_{\ell>2}\big(1-(\ell-1)^{-2}\big)
       \prod_{\substack{\ell\mid N\\\ell>2}}\frac{\ell-1}{\ell-2}
 =\mathfrak S(N).
\]
Consequently the coefficient of \(\log(N-y)\) in the continuous integral vanishes to power accuracy, while the term \(-2\log d\) contributes \(2\mathfrak S(N)\) (the derivative of \(d^{-s}\) includes a minus sign). This proves the claimed squarefree main term.

The missing part is not just an error in the preceding calculation. Even on a squarefree semiprime \(m=rs\), \(s<r\), the full \(H(m)=2\log s>0\), but it is canceled exactly by its parity-twisted copy because \(\mu(m)=1\). Thus obtaining a positive prime-pair count requires controlling the true \(\mu(N-p)H_D(N-p)\) correlation and the remaining divisor bands together, not merely improving the untwisted main term.


For the untwisted divisor strip \(D<d<\sqrt m\), the elementary absolute Brun–Titchmarsh bound gives \(O_B(X(\log\log X)^2)\), since the weight is \(O_B(\log\log X)\) and \(\sum_{D<d\le\sqrt X}\varphi(d)^{-1}\ll_B\log\log X\). More quantitatively, the narrow seam \(1\le m/d^2\le1+\eta\) alone costs \(O(\eta^2 X)\) for \(X^{-1/10}\le\eta\le1/10\). Each contributing \(d\asymp\sqrt X\) gives one reflected-prime progression in an interval of length \(O(\eta X)\); Brun–Titchmarsh bounds its log-weighted mass by \(O(\eta X/\varphi(d))\), since \(\eta X/d\) has polynomial size. Multiply by \(\log(m/d^2)\ll\eta\) and sum \(\varphi(d)^{-1}\) over \(d\asymp\sqrt X\), which is bounded. This absolute estimate also holds with the factor \(\mu(m)\) inserted. It does not pay the whole remaining logarithmic strip.
