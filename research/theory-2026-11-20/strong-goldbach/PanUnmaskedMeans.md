# Uniform vanishing of every unmasked Pan divisor mean

Let \(P\) be the even target, \(L=\log P,\ Y=\sqrt{P}L^{-20}\), and let \(a_P(n)=\sum_{b\mid n,b>Y}\mu(b)\log b\) be the first coefficient of [Huang–Li (6)](https://arxiv.org/html/2005.03811v2#S1). For arbitrary fixed \(C,A>0\), **uniformly** for integers \(1\le d\le P^C\) and \(0\le t\le P\),
\[
 \left|\sum_{n\le t,(n,d)=1} a_P(n)\right|\ll_{A,C} P L^{-A}.
\]
Differences give arbitrary subintervals, with the *same fixed* \(Y\) for both endpoints.

By \(\sum_{b\mid n}\mu(b)\log b=-\Lambda(n)\), the sum equals
\[
 -\sum_{n\le t,(n,d)=1}\Lambda(n)
 -t\frac{\phi(d)}d\sum_{b\le Y,(b,d)=1}\frac{\mu(b)\log b}{b}
 +O(\tau(d)Y L).
\]
Here the error is from inclusion–exclusion when counting unit multiples of coprime \(b\); it is \(P^{1/2+o(1)}\). PNT gives the first term \(-t+O_A(PL^{-A})\) uniformly: for \(t<P/L^{A+2}\) use Chebyshev, and removing primes dividing \(d\) costs \(O_C(L^2)\).

For the truncated sum use the Euler-product identity \(\mu 1_{(\cdot,d)=1}=\mu *1_{s\mid d^\infty}\). The \(s\le\sqrt Y\) convolution terms have inner sums
\[
 \sum_{k\le Y/s}\frac{\mu(k)}k\log k=-1+O_H(L^{-H}),\qquad
 \sum_{k\le Y/s}\frac{\mu(k)}k=O_H(L^{-H}).
\]
These follow from the classical log-saving Mertens estimate, partial summation, and \((1/\zeta)'(1)=1\). The latter sum is multiplied by \(\log s\). For \(\eta=1/\log L\),
\[
 \sum_{s\mid d^\infty}s^{-1+\eta}
 =\prod_{p\mid d}(1-p^{-1+\eta})^{-1}\ll_C L^{O(1)}.
\]
Indeed for \(p\le L^2\) we have \(p^\eta\le e^2\) and use the prime harmonic bound (small-prime factors separately). For \(p>L^2\) there are at most \(CL/\log2\) factors, each \(p^{-1+\eta}\ll L^{-2}\). Hence the harmonic tail for \(s>\sqrt Y\) is \(\ll_C Y^{-\eta/2} L^{O(1)}\), still negligible after any fixed log powers from trivial inner sums. Thus the truncated sum is \(-\sum_{s\mid d^\infty}1/s+O_A(L^{-A})=-d/\phi(d)+O_A(L^{-A})\), as claimed.

Since \(\sum_{d\le P^C}1/\phi(d)\ll_C L^{O(1)}\), **any subset** of unmasked \(d\)-means, even in absolute sum and with an additional \(\log d\) factor, is negligible. In particular [the entire cubic-prefix subcolumn](PanTripleFactorableColumns.md) vanishes *without centering it*, as does the eliminated complete smooth-modulus subcolumn of [the polynomial roughness result](PanPolynomiallyRoughSurvivors.md). The conclusion is NOT asserted for means with additional restrictions on the integers \(n\), such as roughness. This elementary cancellation adds no control over the remaining residue fluctuations.
