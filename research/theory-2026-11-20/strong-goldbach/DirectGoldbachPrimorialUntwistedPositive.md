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

## Joint control of both long strips and a sufficient short-twist estimate

The long strips in both halves of the exact identity can also be charged jointly. Write \(P_X=\prod_{\ell\mid X}(1-1/\ell)^{-1}\) and \(U=\log\log X\). For either sign, uniformly for \(T=X^{1/2+o(1)}\),
\[
 \sum_{\substack{n\le T\\(n,X)=1\\\mu(n)=\pm1}}\frac{n}{\varphi(n)}
  =\frac{T}{2P_X}+O_\eta(T^{1-\eta}X^{o(1)}),\qquad 0<\eta<1/2 .
\]
For the unsigned squarefree weight the Dirichlet series factors as \(\zeta(s)G_X(s)\). At a prime not dividing \(X\), the local factor of \(G_X\) is
\((1-\ell^{-s})(1+\ell^{1-s}/(\ell-1))=1+\ell^{-s}/(\ell-1)-\ell^{1-2s}/(\ell-1)\); at a dividing prime it is \(1-\ell^{-s}\). So \(G_X(1)=1/P_X\), and its coefficient series is absolutely bounded by \(X^{o(1)}\) at \(1-\eta\). Convolution with 1 gives the unsigned main at that precision. For the signed weight replace \(\zeta(s)\) by \(1/\zeta(s)\); at nondividing primes the local ratio \((1-\ell^{1-s}/(\ell-1))/(1-\ell^{-s})\) is absolutely summable in the same coefficient norm, and at dividing primes use \((1-\ell^{-s})^{-1}\). RH gives the same power error with no main term. The norm for the dividing primes in each case follows by splitting off finitely many small primes and bounding each large-prime log-factor by an arbitrarily small constant times \(\log\ell\).

The short untwisted main at \(D=\sqrt X/(\log X)^B\), \(B>1\), holds even for arbitrary even \(X\): in its extension keep all squarefree-lift terms \(k\le K=(1+U)^J\), so that the smoothed explicit-formula error costs \(O(X(\log X)^{1-B}(1+U)K)=o(X)\). The continuous extension is power-small by the same uniform \(F_{X,k}\) tail bounds, summed over \(k\), as in the [short-main proof](DirectGoldbachComplementaryMobiusHalf.md). The large-\(k\) band deletion is unchanged.

For the negative untwisted debit charge only \(\mu(d)=-1\). For the positive parity-twisted debit, on actual squarefree rows use \(\mu(m)\mu(d)=\mu(e)\) with \(e=m/d\); charge only \(\mu(e)=+1\). This divisor switch makes the second prime progression modulus \(e\), now between \(\sqrt m\) and \(m/D\), but still \(X^{1/2+o(1)}\). Apply the same weighted Brun–Titchmarsh argument, followed by the displayed harmonic density by partial summation, to both half-strips. For the new strip the weight is \(2\log(e/\sqrt m)\), and its integral with \(de/e\) is \(\log^2(\sqrt m/D)=B^2U^2+O(U)\), as in the original strip. Equivalently, for a completely uniform upper envelope before summing primes, use the range \([c\sqrt X,\sqrt X(\log X)^B]\) and the weight \(2\log(e/\sqrt X)_++O(1)\) on the central support. Both approaches give the same leading constant. Thus if \(T_D\) denotes the genuine short parity-twisted term, the exact untwisted-minus-twisted sum is bounded below by
\[
 2X\mathfrak S(X)I - T_D
     -(4B^2+o(1))\,XI\,U^2/P_X .
\]
In particular, at primorials, for \(B=1.01\) the remaining unestimated \(T_D\) would suffice if it had one-sided upper bound \(0.7X\mathfrak S(X)I\) for every sufficiently large target in that family. This would make the total strictly positive. The numerical threshold is a criterion, not an established bound on \(T_D\). Neither the criterion nor the untwisted theorem proves Goldbach on this family.

## Relation to previous primorial work

Michael Ross records the exact reflection symmetry of sieve conditions at primes dividing the target in [Sifted Symmetry and Sieve Structures of Primorial Goldbach Complements](https://zenodo.org/records/23026131). His [primorial-multiples note](https://zenodo.org/records/22018781) gives the singular-series identity for primorials and multipliers supported on their primes. These are local inputs also used here; the conditional long-strip estimate above does not follow from either identity. An earlier proposed conditional primorial proof was [explicitly withdrawn by the author in version 3](https://zenodo.org/records/22020981): the Vaughan parameters were scaled to the size of the short prime sample, below the least possible nontrivial divisor of the complement, leaving the hypothesized Type II range empty. Here the estimates are for actual complementary-divisor sums in the indicated ranges, with the remaining short signed estimate left open.
