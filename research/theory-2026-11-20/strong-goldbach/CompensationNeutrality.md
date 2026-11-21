# Exact profilewise accounting for a reverse cutoff change

This is an accounting limitation for [CoupledParityCompensation.md](CoupledParityCompensation.md), not an additional zero-discrepancy theorem about actual prime pairs.

Keep \(N=2x\), \(L=\log x\), the true short prime \(s\) with \(x^{.10}<s<x^{.14}\), \(n=sq\in(x/2,x]\), \(m=N-sq\), \((n,N)=1\), and the original \(W_s(q)=K_{P_3}(sq)\). Let \(B_f(q)\) be any of the smooth reverse coefficients in [SmoothReverseCoreShield.md](SmoothReverseCoreShield.md), allowing signed fixed compact cutoff averages of total 1 as in the coupled note, with the same fixed \(Y=x^{.070}\).

Fix an integer \(k\ge2\) and a fixed compact exponent profile \(\mathcal P\) in the sorted \(k\)-factor simplex, with each coordinate bounded strictly above \(.070\). Its boundaries are finitely many affine walls, with regions on either side specified independently of \(s,q,N\). Let \(F(m)\) vanish off the actual distinct-prime products
\(m=p_1\cdots p_k\), \(p_1<\cdots<p_k\), in this profile and \(m\in[x,3x/2)\). On the profile let \(F(m)/\log m\) be any fixed bounded Lipschitz function of the log proportions \(\log p_i/\log m\). This covers the actual profiles at the fixed macro-rough threshold in the coupled note, modulo the already paid rank-five boundary. One may equally restrict to any fixed subregion of that type. Then with exactly the same normalization as the original opened row, uniformly in the fixed even target,
\[
\begin{split}
\mathcal T_{\rm p}(F)-\mathcal T_f(F)
   &= \mathcal R(F)+O_D(xL^{-D}),\\
\mathcal R(F)
   &=\sum_{\substack{x^{.10}<s<x^{.14}\\ s\ {\rm prime},\ (s,N)=1}}
        \frac{\mathfrak S(Ns)}{s-1}
        \sum_{\substack{x\le m<3x/2\\(m,Ns)=1}}
        \frac{F(m)\, W_s((N-m)/s)}{\log((N-m)/s)}
\end{split}
\tag{1}
\]
for any fixed \(D>0\). Here \(\mathcal T_{\rm p}(F)\) is the actual sum with true \(q\) prime and \(\mathcal T_f(F)\) is the actual integer-\(q\) sum with multiplier \(B_f(q)\). The inner reference in (1) is over actual prime-product \(m\), **not** over those \(m\) for which \((N-m)/s\) is an integer; that class was replaced by its reduced progression mean. In particular the wholly summed changing-cutoff term **on this single reflected profile** satisfies
\[
       \sum_{s,q}W_s(q)F(m)(B_{f_1}(q)-B_{f_2}(q))
                   =O_D(xL^{-D}).
\tag{2}
\]
The model-free content of (2) is on actual physical rows; it does not say that the contributions of their separate \(q\) sectors agree.

## Proof

Use first a single fixed sharp reverse parameter \(U=Y^u\) with \(u\) in a compact subinterval of \((0,1)\), retaining high \(r>U,k'>Y\). Exact reverse Vaughan on the central \(q\), which is \(>Y\), gives
\[
   \Lambda(q)-\sum_{\substack{rk'\mid q\\r>U,\ k'>Y}}\mu(r)\Lambda(k')
       =\sum_{r\mid q,\ r\le U}\mu(r)\log(q/r)
         -\sum_{\substack{rk'\mid q\\r\le U,\ k'\le Y}}\mu(r)\Lambda(k').
\tag{3}
\]
Indeed the low \(k'\le Y\) convolution with all \(r\mid q/k'\) is zero, so the omitted high-\(r\) pieces are minus the low-\(r\) pieces. The proper prime powers in replacing actual \(q\) primes by \(\Lambda(q)/\log q\) are power-small in the global physical divisor envelope: for a fixed \(s\) their count is \(O((x/s)^{1/2}L^C)\), and \(\sum_{s\le x^{.14}}s^{-1/2}\ll x^{.07}\).

For each short divisor \(e=r\) or \(e=rk'\), the literal progression on \(m\) for \(e\mid q\) is \(m\equiv N\pmod{se}\); if \((se,N)>1\) no physical unit contribution is possible. Otherwise the reduced main has modulus factor \(1/\phi(se)\) and support \((m,seN)=1\), including the original \((m,N)=1\) mask. Every prime of \(e\) is \(\le Y\), while every selected prime factor of \(m\) exceeds \(Y\) eventually, so \((m,e)=1\) automatically. Also \((s,e)=1\) since \(s>Y\), and hence the reference unit mask is exactly \((m,Ns)=1\) while \(1/\phi(se)=1/((s-1)\phi(e))\). The physical test \(W_s((N-m)/s)/\log((N-m)/s)\) has bounded variation at the central scale (with the evident \(L^{-1}\) bound); in the first term split \(\log(q/r)=\log q-\log r\). Thus the correct reference divisor is the **physical** \(\log((N-m)/s)\), not \(L\) or a logarithm of \(m\).

The errors in these replacements have arbitrary log reserve by [Maynard I, Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733) at the full \(m\)-scale: every \(se\le x^{.28}\), and the genuine product on this compact profile has a grouping with both lengths polynomial and one short true SW prime. For the exact log-profile weights, use log-fine boxes of width \(L^{-K}\) in each \(\log p_i/L\), with true prime intervals (PNT provides arbitrary SW log reserve for their prefixes). The ordinary product cutoff and the \((m,N)\) mask are imposed as in [FullScaleConvolutionBV.md](FullScaleConvolutionBV.md). At fixed modulus \(se\) all decompositions into \(s,e\), or \(s,r,k'\), have divisor multiplicity; the divisor-weighted BV error follows by Cauchy against the trivial \(O(x/\phi(se))\) bound for each normalized bounded \(m\)-profile sequence in its progression. Summing over logarithmically many boxes and the physical partial-summation intervals is harmless with arbitrary log reserve.

For completeness, a box incident to an affine profile wall lies where a fixed nontrivial linear combination of \(\log p_i/L\) is within \(O(L^{-K})\) of zero: multiply the normalized log-proportion condition by \(\log m/L\). Fix all but a coordinate with nonzero coefficient; the possible remaining factor lies in a relative interval \(O(L^{1-K})\) and is at least \(x^{a_0}\) for some fixed \(a_0>.070\). Summing the integer-count envelope gives \(O(xL^{-K+C}+x^{1-a_0+o(1)})\) physical products near each wall. Indeed the main reciprocal sum over the other factors is \(O(L^{k-1})\), and their product is \(O(x^{1-a_0})\) with only fixed divisor multiplicity. The same argument covers the sorted inequalities and central product endpoints (duplicates themselves power-small). Actual sums in (3) are divisor-bounded **at each physical point since the short factors divide \(q\)**; pay the wall loss using global physical divisor moments, also covering the multiplicity of \(s\mid n\). The main reference wall error has at most a log-power harmonic multiplier over \(s,e\). For the Lipschitz interior test the box approximation is uniformly \(O(L^{-K+C})\) in the normalized weight. Thus the asserted approximation remains valid in both actual and centered sums.

Now in the first main at a fixed physical \(m\), the coprime condition on \(r\) is \((r,Ns)=1\) (adjoining \(s\) does not restrict this range). Its two finite \(\mu/\phi\) moments at \(U\), from (11) of [UnmarkedSemiprimeWholeTypeI.md](UnmarkedSemiprimeWholeTypeI.md), give
\[
 \sum_{\substack{r\le U\\(r,Ns)=1}}
       \frac{\mu(r)}{\phi(r)}\log(((N-m)/s)/r)
      =\mathfrak S(Ns)+O_D(L^{-D}).
\]
Here expanding \(\log U\) times the constant moment is absorbed by taking more log reserve. In the second main fix \(k'=p^j\) with \((k',Ns)=1\), and use \(1/\phi(rk')=(1-p^{-1}1_{p\mid r})/(\phi(r)\phi(k'))\). For the overlap write \(r=p r'\) with \((r',p)=1\) on the nonzero Möbius support. When \(p\le\sqrt U\) its endpoint \(U/p\) is polynomially long, so the constant \(\mu/\phi\) moment has arbitrary log reserve. When \(p>\sqrt U\), instead bound the entire overlap absolutely by
\[
      (p(p-1))^{-1}
        \sum_{r'\le U/p}\frac{1}{\phi(r')}
              \ll \frac{L^C}{p^2},
\]
before multiplication by \(\Lambda(k')/\phi(k')\); if \(p>U\), it is empty. Thus that main is log-small also when the reverse cutoffs are unequal, including \(Y>U\). All short moments and errors are uniform in a fixed compact support in \(u\). Average (3) against the smooth signed density of total 1 and use the above physical identity to prove (1). Subtraction gives (2).

For the two-way correction \((Z_1-Z_0)(B_1-B_2)\) of the coupled note, the function \(Z_1-Z_0\) on each of its fixed macro prime-product profiles satisfies exactly the weight hypotheses of (1). Hence that correction contributes zero to arbitrary log accuracy after summing **all** actual \(q\) there. One cannot count the gains on selected \(q\) sectors as net new slack on such a reflected profile without a bound for the compensating complement. Formula (1) identifies the remaining quantity as the genuine prime-quotient frequency on fixed shifted prime products relative to its explicit reference, not as another freedom in the reverse cutoff.

The supported fixed-profile centering uses the imported Maynard distribution and classical harmonic moments, not additional Goldbach claims. See [the coupled note's comparison](CoupledParityCompensation.md#comparison-with-2026-work) with the dated Arneth and Pham manuscripts.
