# Removing power-smaller conductors from the true triangular parity term

For every fixed even target, Dirichlet GRH makes the principal conductor and all conductors \(\le N^{1-\delta}\) negligible in the exact reflected squarefree parity term, for each fixed \(\delta>0\). This is an arithmetic reduction for the genuine triangular Möbius weight, valid for all even targets, not just powers of two. It does not control the signs of the remaining character pairings.

Put \(X=N\). Let \(f,g\) be fixed smooth real tests compactly supported in \((0,1)\) (the original single reflected test is a product of this kind). Write
\[
 H_{D_0}(m)=\sum_{\substack{d\mid m,\ d\le D_0\\d<\sqrt m}}\mu(d)\log(m/d^2),
 \qquad B(m)=\mu^2(m)\mu(m)H_{D_0}(m)g(m/X),
\]
where \(D_0\le\sqrt X\) may include the whole triangle. Set \(A(p)=\log p\,f(p/X)\) at primes and zero elsewhere. On \([1,X)\), omitting \(p\mid N\) costs \(X^{o(1)}\) in the fixed-target convolution by the divisor bound; in the remaining rows \(m=N-p\) is a unit exactly when \(p\) is. On the units set \(A_\chi=\sum_pA(p)\chi(p)\) and \(B_\chi=\sum_mB(m)\chi(m)\). Character orthogonality gives the exact pairing
\[
 \sum_{\substack{p+m=N\\(pm,N)=1}} A(p)B(m)
 =\frac1{\varphi(N)}\sum_{\chi\bmod N}\chi(-1) A_\chi\overline{B_\chi}.
\]
The ranges \(1\le p,m<X\) make this an exact equation, not an average of neighboring targets.

## Nonprincipal triangular twists

On Dirichlet GRH the two sequences \(\mu(v)\chi(v)\) and, for nonprincipal \(\chi\), \(\mu^2(u)\chi(u)\) have prefix bounds \(O_\epsilon(Y^{1/2+\epsilon}X^\epsilon)\) for \(Y\le X\) and modulus at most \(X^C\), where \(C\) is any fixed constant. For \(\mu\), apply the reciprocal bound and Perron argument in the [reflected Type I note](DirectGoldbachReflectedMobiusTypeI.md). For \(\mu^2\), the Dirichlet series is \(L(s,\chi)/L(2s,\chi^2)\). The numerator is holomorphic for nonprincipal \(\chi\) and obeys the same subpower estimate in a fixed half-plane to the right of \(1/2\) under GRH (the Littlewood logarithm proof applies to \(L\) as well as its reciprocal); the second factor is in absolute convergence. Thus the same Perron proof applies to its bounded coefficients. Additional coprimality with a polynomially bounded integer is effected by inducing the character to the enlarged modulus. Its core stays nonprincipal.

On squarefree \(m=de\), the product of the two Möbius factors at \(d\) and \(m\) is \(\mu(e)\). Therefore \(B_\chi\) is a sum over \(d\le D_0,e>d\) with coefficients \(\mu^2(d)\mu(e)\chi(de)1_{(d,e)=1}\) and smooth product weight \(g(de/X)\log(e/d)\). Use dyads \(d\asymp D\), \(e\asymp E\); on every nonempty dyad \(DE\asymp X\). Open \(1_{(d,e)=1}=\sum_{k\mid d,e}\mu(k)\) and put \(d=ku,e=kv\). Only squarefree \(k\) need be considered; for nonzero terms the factorizations give \(\mu^2(ku)=\mu^2(u)1_{(u,k)=1}\) and \(\mu(kv)=\mu(k)\mu(v)1_{(v,k)=1}\). The extra unit conditions are again induced characters, and the constant coefficient has modulus at most one. Both one-variable prefixes can now be bounded independently.

The cutoff \(e>d\) introduces no power loss in two-dimensional partial summation. In logarithmic dyad coordinates \(x=\log(u/(D/k))\), \(y=\log(v/(E/k))\), the weight equals a smooth function of \(k^2uv/X\) times \((y-x+\log(E/D))_+\). The smooth factor and its first and mixed derivatives are uniformly bounded on the dyad. The positive part has bounded edge variation; its mixed distributional derivative is a delta measure on a straight line of bounded mass if it crosses the rectangle. Its sup is \(O(\log X)\), so the total mixed variation and the edge variations of the product are \(O(\log X)\), sufficient for two-dimensional Abel summation. A sharp \(d\) cap only truncates the rectangle.

For each \(k\) the resulting bound is \(O_\epsilon(\sqrt{D/k}\sqrt{E/k}\,X^\epsilon)\) absorbing log powers and shrinking internal epsilons. Sum over \(k\ll D\) and the dyads, using the harmonic series. This proves \(B_\chi\ll_\epsilon X^{1/2+\epsilon}\) uniformly for all nonprincipal characters, with the original triangular cutoffs retained.

## Which conductors are paid

For each nonprincipal character, GRH and partial summation on the genuine prime weight give \(A_\chi\ll_\epsilon X^{1/2+\epsilon}\). For the principal character, hold \(d\) fixed and apply the one \(\mu(e)\) prefix estimate with \((e,dN)=1\); summing \(O_\epsilon(\sqrt{X/d}\,X^\epsilon)\) over \(d\le\sqrt X\) gives \(B_{\chi_0}\ll_\epsilon X^{3/4+\epsilon}\). Since \(A_{\chi_0}\ll X\) and \(\varphi(N)\gg N/\log\log N\), the principal contribution is power-small.

The number of characters of conductor \(q\mid N\) is at most \(\varphi(q)\). Thus at most \(X^{1-\delta}\tau(N)\) nonprincipal characters have conductor at most \(X^{1-\delta}\); after division by \(\varphi(N)\), their aggregate is \(O_\delta(X^{1-\delta/2})\) on choosing the epsilons small. This is valid even if the eligible \(q\)'s are not themselves prime powers.

However high conductors account for almost all characters by this same count, and the individual square-root-scale estimates cannot be summed there to give a strict saving. At \(N=2^k\) this limitation appears transparently in unsigned energy: for tests whose supports have width \(<N/4\), orthogonality and subtraction of the characters induced from \(N/2\) give primitive energy exactly half the diagonal under \(1/\varphi(N)\) normalization. For each nonzero test the prime diagonal has order \(N\log N\). The full-triangle \(B\)-diagonal has at least that order too, already from prime \(m\), where \(B(m)=-g(m/N)\log m\). Thus a bound based only on separate unsigned energies has a Cauchy–Schwarz scale at least \(N\log N\). This is not a lower bound on the signed correlation. The remaining task is joint control of the high-conductor pairings, or a different estimate for the same true parity contribution.
