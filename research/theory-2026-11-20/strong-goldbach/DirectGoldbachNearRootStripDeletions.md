# Two absolute deletions in the genuine near-root Möbius strip

This reduces the [unresolved near-root part](DirectGoldbachComplementaryMobiusHalf.md) for every fixed even \(N\). It does not estimate the sign of the remaining core. No GRH is needed for the deletions.

Write \(X=N\), \(L=\log X\), \(D=\sqrt X/L^B\) with fixed \(B\), \(m=N-p=de\), \(D<d<e\), and keep the original smooth interior test on \(p/X\). Thus both \(d,e\) lie in \([D,C\sqrt X L^B]\), and \(\log(e/d)\ll_B1+\log\log X\). Use the log-prime weight on \(p\). In particular all relevant \(p\asymp X\). A fixed-size interval at \(X\), or any subset with a bounded smooth weight, has log-prime mass \(O(X/\varphi(q))\) in each reduced residue class with modulus \(q\le X^{.53}\) by Brun–Titchmarsh. A nonunit class \(N\bmod q\) cannot contribute because \(p>q\).

## The squarefree lift needs only a power of \(\log\log X\)

Open the squarefree factor \(\mu^2(m)=\sum_{k^2\mid m}\mu(k)\) and discard \(k>K\). On the untwisted side \(d\) is squarefree because it is weighted by \(\mu(d)\); on the twisted side use \(\mu^2(d)\mu(e)\) on squarefree rows before opening the lift, retaining \(\mu^2(d)\) in the extension to unrestricted \(m\). In either case the other arithmetic weights have modulus at most one. For squarefree \(K<k\le X^{.01}\), put \(h=(d,k)\) and \(d=hj\). With \(q=[d,k^2]=k^2j\) and \((j,k)=1\), one has \(\varphi(q)=\varphi(k^2)\varphi(j)\). For any \(h\mid k\) the allowed interval for \(j\) has \(\sum 1/\varphi(j)\ll_B1+\log\log X\). To see the requisite uniformity, use \(n/\varphi(n)=\sum_{\ell\mid n}\mu^2(\ell)/\varphi(\ell)\): for \(1\le A\le B'\) the harmonic inner interval with endpoints divided by \(\ell\) is \(O(1+\log(B'/A))\), and the outer \(\sum_\ell1/(\ell\varphi(\ell))\) converges. Here \(D/h\gg1\) and the interval ratio is at most a fixed log power. The moduli in this range are at most \(X^{.52}\). Thus the absolute cost here is at most
\[
 \ll_B X(1+\log\log X)^2\sum_{k>K}\frac{\tau(k)\mu^2(k)}{\varphi(k^2)}
 \ll_B X(1+\log\log X)^2 \frac{(\log(2K))^3}{K}.
\]
For squarefree \(k\), \(\tau(k)/\varphi(k^2)\le d_4(k)/k^2\), and the standard divisor summatory bound gives the last inequality. The tail \(k>X^{.01}\) costs at most \(X^{.99}\log^C X\) by counting multiples of \(k^2\) with weight at most \(\tau(m)\log^2 X\), splitting \(\tau(k^2l)\le\tau(k^2)\tau(l)\) and using \(\tau(k^2)\le d_3(k)\). Thus \(K=(1+\log\log X)^J\) for a fixed sufficiently large \(J\) makes the total \(o(X)\); \(J\) can give any prescribed fixed power saving in \(\log\log X\).

## Remove divisors having a nearly square-root prime factor

In the true squarefree strip, take \(0<\eta\le1/10\) and \(z=X^{1/2-\eta}\). If either of the two divisors, called \(a\), has a prime \(\ell\ge z\), write \(a=\ell j\); here \((\ell,j)=1\) exactly. The same prime progression bound in modulus \(a\) applies symmetrically to either choice of divisor. Sum \(1/\varphi(j)\) over the allowed multiplicative interval as above, and then over \(z\le\ell\le C\sqrt X L^B\). The prime reciprocal sum in this range is \(O_B(\eta+(1+\log\log X)/L)\), by the prime number theorem with its classical remainder and partial summation. Including both choices of \(a\) and the logarithmic ratio weight, the absolute cost is
\[
 O_B\!\left(X(1+\log\log X)^2
 \left(\eta+\frac{1+\log\log X}{L}\right)\right).
\]
Take \(\eta=(1+\log\log X)^{-4}\). This removes \(o(X)\) and leaves both factors composed of primes below \(X^{1/2-\eta}\). In particular neither divisor is prime; each has a proper divisor at least \(X^\eta/L^B\), by dropping its largest prime factor. This size is subpolynomial in \(X\) and does not by itself provide an available fixed-power factorability estimate.

## An obstruction to a uniform short Möbius coefficient bound

Let \(N=\prod_{\ell\le y}\ell\), so \(\log X\sim y\), and take \(U=y^C\), with any fixed \(1<C<2\). For every \(r\le X\) coprime to \(N\), every integer \(t\in(U,2U]\) coprime to \(rN\) is prime: its prime factors exceed \(y\), and \(2U<y^2\) for large \(y\). The primes disallowed by \(r\) number at most \(\log X/\log U\). Their reciprocal cost \(O(y/(U\log y))\) is negligible, so the PNT gives, uniformly in \(r\),
\[
 \sum_{\substack{U<t\le 2U\\(t,rN)=1}}\frac{\mu(t)}{\varphi(t)}
 =-\frac{\log2+o(1)}{C\log y}.
\]
Consequently no bound \(O((\log X)^{-\epsilon})\) for these relative-modulus coefficients is uniform in the target for any fixed \(\epsilon>0\). This does not estimate cancellation among the genuine corresponding prime progression errors.
