# A positive-mass obstruction in the exact doubly high ledger

The current dual log-conservation reduction leaves a signed \(.010 M_N\) sufficient upper criterion only on genuinely high prime marks. Even after the verified removals, a surviving family of bare semiprime-by-semiprime rows has **positive dyadic mass greater than \(.0139 M_N\) in normalized mean**. Thus replacing the untreated signs by a nonnegative envelope cannot establish the present criterion. No conclusion about the signed mean at any particular target is asserted.

## 1. The actual live ledger and the test family

Use the short smooth kernels \(h,f\) of [ReverseLargeTagShoulder](ReverseLargeTagShoulder.md), each with positive-side support at most \(.001\), \(h=1,\ f(t)=1-t\) near zero. Let \(N=2x\) even, \(L=\log x\), \(s\) true prime in \(x^{.10}<s<x^{.14}\), \(n=sq\in(x/2,x]\), \(m=N-n\), \((n,N)=1\), and \(M_N=\mathfrak S(N)x/(2L)\). The unchanged signed remainder after the two low-prime log balances is
\[
 E_N=
 \sum_{\substack{s,q;\ q,m\ {\rm composite}\\
                  p\mid q,\ r\mid m\ {\rm true\ primes}\\
                  p>x^{.359},\ r>x^{.499}}}
    W_s(q)H_h(q)H_f(m)\frac{\log p}{\log q}\log r
       +o(M_N).                                                       \tag{1}
\]
This is [DualPrimeLogConservation](DualPrimeLogConservation.md), (3), with the raised cutoffs justified in [ReverseLargeTagShoulder](ReverseLargeTagShoulder.md), Section 6. In particular the low reflected \(+.501 J M_N\) and dual low-\(p\) \(-.501 J M_N\) cancel, where \(J=\log(7/5)-.1408\). The sufficient threshold on the signed remaining sum is the original \(.010 M_N\), with strict room for the \(o(M_N)\); this is not the larger threshold of an earlier one-tag ledger, nor the reserve of a broader choice of kernel.

Consider the following genuine physical subset:
\[
 q=p u,\qquad m=r v,\qquad u,v\ {\rm prime},\qquad
 .455\le\alpha=\log_xp\le.555,\quad .560\le\beta=\log_xr\le.680.
                                                                    \tag{2}
\]
The \(s\) band is unchanged. In (2), \(u\) has exponent between \(.305\) and \(.445\) up to \(O(1/L)\), hence \(u<p\), and \(v\) has exponent \(.320\)–\(.440+O(1/L)\), hence \(v<r\). Thus the marked primes are exactly the larger prime on their respective legs, all factors are polynomially rough and, for sufficiently large \(x\), \(H_h(q)=H_f(m)=1\) exactly. These terms have the positive original weight \(W_s(q)(\log p/\log q)\log r\).

The family (2) genuinely survives the relevant verified deletions in the **same tagged sum**:

* Both tags exceed the two low log cutoffs. The previous absolute tiny-prime and squareful removals do not remove these rows; \(q,m\) have distinct prime factors and the smallest has exponent \(>.300\) for large \(x\).
* The forward taper is only at \(r<x^{.506}\). The first four raised forward/reverse strips are at \(\beta\le .535\); the fifth and sixth require \(\alpha<.387\) or \(<.367\) respectively. The [literal below-half mask](BelowHalfLiteralBalance.md) does not contain \(\beta\ge.560\).
* Here \(p r\ge x^{1.015}\), and \(s p r\) is strictly larger still. Thus neither the elementary determinant cancellation nor the [whole subcritical spectral sector](SpectralSubcriticalPrimeProduct.md), including its earlier central spectral box, removes these terms.
* The [unmarked Wright sector](WrightSupercriticalPrimeProduct.md) requires \(p>r\), whereas in (2) \(p<r\) throughout. The [Ramaré-marked Wright sector](WrightSupercriticalRoughMarker.md) has \(r\) near exponent \(.51\) and requires an extra prime factor of \(u\) near exponent \(.021\); here the actual \(u\) is itself a single prime \(>x^{.300}\).
* The [giant-reflected sector](GiantReflectedSupercriticalTransfer.md) requires \(2(1-\beta)+\sigma+2\alpha<1\). In (2) the left side is at least \(2(.320)+.100+2(.455)=1.650\).
* Signed results for earlier kernels or reorganized ledgers do not supply another deletion or reserve in (1). Also the same integer \(q\) may have a second eligible prime tag \(u\) belonging to a deleted sector. Such a result removes that **different tagged contribution**, not the term at its larger prime \(p\) used in (2).

Write \(P_N\ge0\) for the sum on (2) including the literal \((n,N)=1\) condition.

## 2. Independent prime counts across the two legs

Let \(Y\to\infty\), \(L_Y=\log Y\), and aggregate over the even \(N\) with \(Y\le x=N/2\le2Y\). First keep the exponent ranges at scale \(Y\), with every interval shrunk on both ends by a small fixed \(\epsilon>0\). These rows lie in the declared scale-\(x\) ranges for large \(Y\) since \(\log x=L_Y+O(1)\). At the end take \(\epsilon\downarrow0\). Throughout the fixed central geometric region \(n,m\asymp Y\).

For a fixed \(n\)-interval \(I_n\) whose endpoints are positive fixed multiples of \(Y\), first fix the true primes \(s,p\) and count \(u\) in \(I_n/(s p)\) by the prime number theorem. Uniformly in the selected boxes, this is
\[
 (1+o(1))\frac{|I_n|}{s p\, (1-\sigma-\alpha)L_Y},
           \qquad \sigma=\log_Y s,\quad \alpha=\log_Yp .
\]
The denominator is uniformly polynomially large in its underlying prime scale; this application uses intervals of fixed relative length, not a power-short PNT. Uniformly on this \(n\)-interval,
\[
 W_s(q)\frac{\log p}{\log q}
      =W(\sigma)\frac{\alpha}{1-\sigma}+O(1/L_Y),
      \qquad W(t)=(1-t)(1-2t)^2.
\]
Summing over \(s,p\) by the PNT prime reciprocal law with continuous bounded tests gives
\[
 \frac{|I_n|}{L_Y}\left(
       \int_{I_\sigma}\frac{(1-2\sigma)^2}{\sigma}
                   \int_{I_\alpha}\frac{d\alpha}{1-\sigma-\alpha}
                   \,d\sigma+o(1)\right).                              \tag{3}
\]
Here the prime harmonic measures are \(d\sigma/\sigma\), \(d\alpha/\alpha\), and the factor \(\alpha\) in the marked weight has canceled the latter denominator. Each triple labels its \(n\) uniquely for this population: \(s\) is the only prime in its small band and \(p>u\).

For a fixed \(m\)-interval \(I_m\), fix \(r\) and count the true prime \(v\) in \(I_m/r\) similarly. Its log is \((1-\beta)L_Y+O(1)\), and the original \(\log r=\beta L_Y\) cancels both the log scale and the prime harmonic denominator for \(r\). The weighted result is
\[
   |I_m|\left(\int_{I_\beta}\frac{d\beta}{1-\beta}+o(1)\right).          \tag{4}
\]
Parity is not an extra factor in (3)–(4): each product uses only odd primes for large \(Y\), so every independent pair \(n,m\) yields even \(N=n+m\).

The only possible common prime between the two products \(n=s p u\) and \(m=r v\) is \(u=v\). On the scale-\(Y\) ranges such a prime is \(>Y^{.300}\) for large \(Y\). At a fixed \(u=v\), allowing integers on the remaining \(p,r\) axes costs
\(O((Y/u)L_Y+Y^{.14})\) possibilities for \(s,p\) and \(O(Y/u+1)\) for \(r\). In the actual overlap range \(u=v\le Y^{.441}\), \(Y/u\) dominates \(Y^{.14}\). The sum over such \(u\), even over all integers \(u>Y^{.300}\), is \(O(Y^{1.700}L_Y)\) unweighted and \(O(Y^{1.700}L_Y^2)\) in the above weights. It is power-small relative to \(Y^2/L_Y\). Thus discarding incompatible \((n,N)>1\) from the pair product does not change the limiting lower mass.

The polygon \(Y\le (n+m)/2\le2Y,\ (n+m)/4<n\le(n+m)/2\) has area
\[
       \int_{2Y}^{4Y}\frac N4\,dN=\frac32Y^2 .
\]
Approximate its interior by finite unions of fixed axis-parallel rectangles after dividing \(n,m\) by \(Y\). On each rectangle multiply (3) and (4), and then discard the common-prime possibilities just bounded. Taking the rectangles to exhaust the polygon, and next the exponent shrinkage \(\epsilon\downarrow0\), gives the lower asymptotic
\[
 \liminf_{Y\to\infty}\frac{\sum_{Y\le N/2\le2Y,\ N\ {\rm even}}P_N}
                           {(3/2)Y^2/L_Y}
  \ge
  \left(\int_{.100}^{.140}\frac{(1-2\sigma)^2}{\sigma}
        \int_{.455}^{.555}\frac{d\alpha}{1-\sigma-\alpha}\,d\sigma\right)
     \log\frac{.440}{.320}.                                           \tag{5}
\]
This is only a dyadic aggregate; the argument has not changed the weights in any fixed-target row.

## 3. Normalization and strict numerical lower bound

For \(N=2k\), \(\mathfrak S(2k)=2C_2\sum_{d\mid k}\rho(d)\), where
\(\rho(d)=\mu^2(d)1_{2\nmid d}\prod_{\ell\mid d}(\ell-2)^{-1}\). Since \(\rho(d)\ll_\eta d^{-1+\eta}\) for fixed \(\eta>0\), summing floors over \(k\le Z\) and extending \(\sum \rho(d)/d\) to infinity gives
\(\sum_{k\le Z}\mathfrak S(2k)=2Z+o(Z)\). Indeed
\(\sum_d \rho(d)/d=\prod_{\ell>2}(1+1/[\ell(\ell-2)])=1/C_2\).
Partial summation with \(k/(2\log k)\) gives
\[
     \sum_{Y\le N/2\le 2Y,\ N\ {\rm even}} M_N
               =\left(\frac32+o(1)\right)\frac{Y^2}{L_Y}.               \tag{6}
\]
This is the actual weighted normalization \(\sum P_N/\sum M_N\), not an unweighted mean of the ratios.

Since \(1-\sigma-\alpha\le .445\) throughout the box, (5)–(6) are bounded below by
\[
        J\,\frac{.100}{.445}\log(11/8)>.0139,\qquad
        J=\int_{.100}^{.140}\frac{(1-2\sigma)^2}{\sigma}\,d\sigma
          =\log(7/5)-.1408 .
\]
The companion checker uses rational lower bounds from the first two positive terms of
\(\log t=2\sum_{j\ge0}((t-1)/(t+1))^{2j+1}/(2j+1)\). Both the normalization and the comparison are therefore strict without a floating-point quadrature.

Consequently, in every sufficiently large dyadic aggregate at least one even target has \(P_N>.0139 M_N\). For a method that keeps only the currently verified exact deletions and then upper-bounds all remaining terms by their nonnegative parts or any pointwise nonnegative envelope above them, that method's bound includes \(P_N\) at those targets, and cannot lie below \(.010M_N\) uniformly. This does not imply the true signed remainder exceeds \(.010M_N\) at any target. Negative terms outside (2), or new signed comparisons that genuinely remove some of its terms, are exactly what the obstruction leaves available.

## 4. A distinct exact obstruction to canceling a centered completion diagonal

There is a separate algebraic check on the proposed sparse double-Cauchy bypass. The following is a statement about the **uniform-unit diagonal model**, not an identity for the actual prime-supported inner norm.

In the true short-divisor opening \((d,e)=1\), \(d,e\) are squarefree and coprime to \(N\). A nonzero Poisson frequency \(j\) can be reduced by putting \(d_1=(j,d)\), \(e_1=(j,e)\), \(d=d_0d_1,\ e=e_0e_1,\ j=k d_1 e_1\). Then \((k,d_0e_0)=1\), because \(d,e\) are squarefree, and
\[
 e_{re}\!\left(jN\overline{s p d}\right)
       =e_{re_0}\!\left(kN\overline{s p d_0}\right).
\]
This uses the exact inverse-unit conditions, cancellation of \(d_1\) against \(j\), and removal of the factor \(e_1\) from the additive modulus. The normalized Fourier argument also becomes \(k x/(s p r d_0e_0)\). When \(s\nmid k\), the reduced denominator of the \(r\)-phase's rational argument \(k/(s d_0e_0)\) determines the true prime \(s\) and the squarefree product \(c=d_0e_0\), but not the allocation of \(c\)'s primes between its two legs. This is the source of same-denominator collision terms. The \(s\mid k\) terms have a different reduced denominator and are not needed for this obstruction.

Fix \(s,k,c,N,r\) in this same-denominator case, with \(c\) squarefree, \((kN,c)=1\), \((r,s c)=1\), and the prime \(s\) coprime to \(c\). Then \(c\) is odd because \(N\) is even. For each allocation \(e_0\mid c\) let \(d_0=c/e_0\), and on \(b\in(\mathbb Z/r c\mathbb Z)^\times\) define the unit phase
\[
 \Phi_{e_0}(b)=e_{r e_0}\!\left(kN\overline{s(c/e_0)b}\right).
\]
Its \(r\)-component is \(e_r(kN\overline{s c b})\), common to all allocations. For each \(\ell\mid c\), the \(\ell\)-component is absent when \(\ell\nmid e_0\), and equals
\(e_\ell(kN\overline{s r(c/\ell)b})\) when \(\ell\mid e_0\); it depends only on the presence bit. The uniform average of the displayed nontrivial \(\ell\)-component over units is \(-1/(\ell-1)\). Therefore the full normalized Gram matrix of all allocation phases is exactly
\[
  G_c=\bigotimes_{\ell\mid c}
            \begin{pmatrix}1&-1/(\ell-1)\\-1/(\ell-1)&1\end{pmatrix}.   \tag{7}
\]
In particular, for arbitrary complex allocation coefficients \(A_{e_0}\), its quadratic form is at least
\[
 \left[\prod_{\ell\mid c}\left(1-\frac1{\ell-1}\right)\right]
       \sum_{e_0\mid c}|A_{e_0}|^2
 \gg \frac{\phi(c)}c\sum_{e_0\mid c}|A_{e_0}|^2.
\]
Indeed the ratio of the two factors at each \(\ell\) is \(1-1/(\ell-1)^2\), with an absolutely convergent positive product over odd primes. Since \(c\) is polynomially bounded in \(x\), \(\phi(c)/c\gg1/\log\log x\), for instance by splitting its primes at \(\log x\) and using the ordinary Mertens product. Thus internal allocation signs in this specific positive norm cannot give any fixed power of \(\log x\) savings over its squared coefficient norm.

Even subtracting the **exact uniform-unit mean** of every \(\Phi_{e_0}\) changes (7) only by \(v v^*\). If \(r\) is the true large prime, \(r\nmid kN\), the \(r\)-component has mean \(-1/(r-1)\), and
\[
       \|v\|_2^2
       =(r-1)^{-2}\prod_{\ell\mid c}\left(1+\frac1{(\ell-1)^2}\right)
       \ll (r-1)^{-2}.
\]
The lower spectral bound is therefore unchanged in size after this model centering. This does **not** prove the same Gram or its lower bound for genuine \(p\)-supported sums in a short interval. It says that a proposed gain must use actual signed prime-supported covariance across **distinct** reduced rational frequencies, or avoid this diagonal norm by a different actual reformulation. Neither exact model centering nor taking a different linear combination of allocations alone supplies that gain.
