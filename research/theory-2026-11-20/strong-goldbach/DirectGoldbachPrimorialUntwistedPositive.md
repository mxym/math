# A positive full untwisted contribution at primorial targets

Assume Dirichlet GRH. Let \(X=N=\prod_{\ell\le y}\ell\) tend to infinity through primorials. For any fixed, smooth, nonnegative interior test \(V(p/X)\) with \(I=\int V>0\), let \(H(m)=\sum_{d\mid m,\ d<\sqrt m}\mu(d)\log(m/d^2)\) as in the [complementary-squarefree identity](DirectGoldbachComplementaryMobiusHalf.md). Then
\[
 \sum_{p\ \mathrm{prime}}\log p\, V(p/X)\mu^2(X-p)H(X-p)
 \ \ge\ (2-4e^{-2\gamma}B^2-o(1))X\mathfrak S(X)I
\]
for every fixed \(1<B<e^\gamma/\sqrt2\). At \(B=11/10\) the lower coefficient is greater than \(0.47\). The parity-twisted half is not covered by this bound.

## Move the short cutoff to \(\sqrt X/(\log X)^B\)

Let \(L=\log X\), and take the earlier short main-term cutoff \(D_0=\sqrt X/L^{B_0}\) with sufficiently large fixed \(B_0>B\). Extend it to \(D=\sqrt X/L^B\). In the extension interval, the [squarefree-lift truncation](DirectGoldbachNearRootStripDeletions.md) costs \(o(X)\) for \(k\le K=(1+\log\log X)^J\) with \(J\) sufficiently large. Since \(y\sim L\), each \(1<k\le K\) shares a prime with \(X\), and on the test support \(p\asymp X\) cannot share it. Thus the extension is evaluated with the \(k=1\) term. Also only \((d,X)=1\) can contribute.

For \(D_0<d\le D\), the fixed smooth prime test \(u\mapsto V(u)\log(X(1-u)/d^2)\) and any fixed number of its derivatives are \(O_{B_0,V}(1+\log\log X)\). The smoothed Dirichlet explicit formula on GRH has reduced progression error \(O(\sqrt X(1+\log d)(1+\log\log X))\) for this test. Indeed its Mellin transform decays faster than any fixed power of zero height with the stated uniform derivative factor; the zero count in each unit height interval is \(O(\log(d(2+|t|)))\), whose weighted sum is \(O(1+\log d)\). Average over characters by orthogonality; removed imprimitive Euler terms are also harmless. Prime powers may be removed across the whole extension at cost \(O_\epsilon(X^{1/2+\epsilon})\) using the divisor bound on \(X-p^j\) and the test's polylogarithmic size. Summing the progression errors over \(d\) costs \(O(X L^{1-B}(1+\log\log X))=o(X)\). The continuous density contribution over \(D_0<d\le D\) is \(o(X)\) by subtracting the two tails of the \(k=1\) Euler series and its derivative from the short-main argument. The full short term at \(D\) is consequently \(2X\mathfrak S(X)I+o(X)\).

## The strip has absolute constant strictly below 2

If \(d\mid m=X-p\) contributes, it has no prime factor \(\le y\), since the test keeps \(p\) above \(y\). In \(D<d<\sqrt X\), \(\varphi(d)^{-1}=(1+o(1))/d\) uniformly: the number of factors is \(O(L/\log y)\) and each contributes \(O(1/y)\) to the logarithm of \(d/\varphi(d)\). Also
\[
 0\le 1_{d<\sqrt m}\log(m/d^2)\le 2\log(\sqrt X/d).
\]
By Brun–Titchmarsh on any fixed relative-length interval within the supported prime range, the log-prime mass in the class \(X\bmod d\) is at most \((4+o(1))\) times interval length divided by \(\varphi(d)\). The 4 comes from the numerator 2 and \(\log(\text{interval length}/d)\sim\frac12 L\). Majorize \(V\) by upper step approximants of arbitrarily small fixed mesh, let \(X\) tend to infinity for each mesh, then take the mesh to zero. Hence the absolute strip is at most
\[
 (4+o(1))XI \sum_{\substack{D<d<\sqrt X\\P^-(d)>y}}\frac{2\log(\sqrt X/d)}d .
\]
In each fixed-ratio box at these scales, the integer fundamental lemma of sieve gives density \((1+o(1))\prod_{\ell\le y}(1-1/\ell)=(e^{-\gamma}+o(1))/\log y\), uniformly. For example, take a fixed power of the box start as sieve level, so the sieve parameter \(\log(\mathrm{level})/\log y\) tends to infinity, with elementary integer remainder negligible. Summation on fixed log-width boxes and integration of the decreasing log weight give
\[
 \sum_{\substack{D<d<\sqrt X\\P^-(d)>y}}\frac{2\log(\sqrt X/d)}d
   =(e^{-\gamma}B^2+o(1))\log\log X.
\]
The integral of \(2t\) from \(0\) to \(B\log\log X\) is \(B^2(\log\log X)^2\), and fixed-box endpoint errors are lower order here. Finally, at primorials the singular series is
\[
 \mathfrak S(X)=\prod_{\ell\le y}(1-1/\ell)^{-1}
                  \prod_{\ell>y}\bigl(1-(\ell-1)^{-2}\bigr)
         =(e^\gamma+o(1))\log\log X.
\]
Thus the strip's absolute weight is at most \((4e^{-2\gamma}B^2+o(1))X\mathfrak S(X)I\). Reverse triangle with the short main gives the claim. Even-squarefree-factor rows, including semiprimes, can have positive untwisted weights that cancel exactly in the prime-pair identity. No assertion of Goldbach for primorials follows.

## One-sided improvement and extension to many small prime divisors

For a lower bound on the strip, only \(d\) with \(\mu(d)=-1\) need be charged. More generally, fix \(e^{-\gamma}<\theta\le1\) and suppose every prime up to \(y=(\log X)^\theta\) divides \(X\). Then for every fixed \(1<B<e^\gamma\theta\) the lower coefficient for the full untwisted term improves to
\[
 2-\frac{2e^{-2\gamma}B^2}{\theta^2}-o(1)>0 .
\]
For primorials this conclusion holds with \(\theta=1\) in the coefficient, using the actual primorial threshold \(y\sim\log X\). At \(B=11/10\) the resulting primorial coefficient is greater than \(1.23\).

The extension of the short term is unchanged: \(y\gg K\) eliminates every \(k>1\) in the truncated extension. Inside fixed multiplicative boxes \(T<d\le e^h T\), \(T=X^{1/2+o(1)}\) and \(h>0\) fixed, the rough \(\mu(d)=-1\) integers have half the rough density, up to \(o(1/\log y)\). To see this, the rough \(\mu^2\) count differs from the rough integer count by \(O_h(T\sum_{\ell>y}\ell^{-2})=o(T/\log y)\). Under RH the signed rough prefix is bounded by \(O_\epsilon(T^{1/2+\epsilon+o(1)})\) by convolving the ordinary Möbius sequence with the indicator of \(y\)-smooth integers: the sum of that convolution factor against \(n^{-1/2-\epsilon}\) is \(\prod_{\ell\le y}(1-\ell^{-1/2-\epsilon})^{-1}=T^{o(1)}\) when \(y\ll\log X\). The negative indicator is \((\mu^2-\mu)/2\).

For \(\theta<1\) it is not necessary to approximate \(1/\varphi(d)\) individually by \(1/d\). On each fixed-ratio box, the aggregate error for rough \(d\) in doing so is \(O_h(1/y)\): expand \(d/\varphi(d)=\sum_{a\mid d}\mu^2(a)/\varphi(a)\), omit \(a=1\), and bound the inner harmonic sum over multiples of \(a\) by \(O_h(1/a)\). Summing over rough \(a>1\) costs at most \(O(\sum_{\ell>y}1/(\ell(\ell-1)))\) by the convergent Euler product. Thus the strip's negative debit is at most
\[
 (2e^{-\gamma}B^2/\theta+o(1))XI\log\log X .
\]
The target's singular series is at least \((e^\gamma\theta+o(1))\log\log X\): all primes up to \(y\) are included, and adding more prime divisors increases the product. This proves the claimed relative debit. It still says nothing about the parity-twisted term.
