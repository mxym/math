# Exact signed conservation across the short reflected-prime logarithmic projection

The broad negative debit from [BroadReflectedLowTagDebit](BroadReflectedLowTagDebit.md) does not make all smaller reflected tags negligible. In fact their compensating **positive** signed main is much larger. This note evaluates the whole subcritical prime-tag projection and isolates one exact remaining operator on actual large reflected primes. The required signed upper on that operator is not established.

## 1. Physical conventions and statement

Keep \(N=2x,\ L=\log x,\ M_N=\mathfrak S(N)x/(2L)\), the same true \(s\) band, \(n=sq,m=N-n\in[x,1.5x)\), central \(n\in(x/2,x]\), units \((n,N)=1\), and weight \(W_s(q)\). Write \(J=\log(7/5)-.1408\), and take **any fixed** \(C_c^\infty\) \(h\) supported on \(t\le .400\) for positive \(t\), exactly 1 near zero, and \(f\) supported on \(t\le .001\) for positive \(t\), exactly \(1-t\) near zero. Both kernels have the original prime atoms, and the original centered sum is
\[
 E_N=\sum_{s,q;\,q,m\ {\rm composite}} X_h(s,q)+O_A(xL^{-A}),\qquad
 X_h=W_s(q)(\log m)H_h(q)H_f(m).
\]
These identities only need short support and the exact affine calibration as in the two preceding smooth notes; \(h\)'s allowed \(.400\) upper bound is unchanged. Put
\[
 V_{\le B}(m)=
 \sum_{\substack{r\mid m,\ r\ {\rm prime}\\r\le x^B}}\frac{\log r}{\log m},
 \qquad V_{>B}(m)=
 \sum_{\substack{r\mid m,\ r\ {\rm prime}\\r>x^B}}\frac{\log r}{\log m}.
\]
For each fixed \(0<B\le .489\) one has
\[
 \sum_{s,q;\,q,m\ {\rm composite}} X_h V_{\le B}
      =-\big(J[B+f(B)-1]+o(1)\big)M_N.                                  \tag{1}
\]
In particular at \(B=.489\) this equals \(+.511 J M_N+o(M_N)\), while at \(B=.003\) it equals \(+.997 J M_N+o(M_N)\) (the stated broad negative term is their difference). These are **literal** weights on actual tags including genuine bounded primes whenever permitted by the unit masks.

It follows that the exact remaining large-mark sum obeys
\[
 E_N=(.511J+o(1))M_N+\mathcal R_N(h,f),\qquad
 \mathcal R_N(h,f)=\sum_{s,q;\,q,m\ {\rm composite}} X_h V_{>.489}(m).
                                                                         \tag{2}
\]
For wide \(h\) allowed here this is its own criterion, without using the previous two-tag \(U V_1\) null. For the short \(.001\) kernel \(h\) of [BalancedLargeTagTaper](BalancedLargeTagTaper.md), one may replace \(V_{>.489}\) in (2) by \(V_{>.489}-U_S V_1\), up to an arbitrary-log error, since that exact null applies and the resulting mark weight stays nonnegative. This does not carry a wide-kernel reserve into the short kernel. The required upper in (2) for the prior \(.010M_N\) sufficient criterion is
\((.010-.511J)M_N\), about \(-.08998851 M_N\), with a fixed strict margin if used for eventual positivity.

## 2. Split a true prime bit, even at high valuation

For any marked prime \(r\mid m\), set \(u_r=\log r/\log m\). The exact divisor identity, **regardless of the exponent of \(r\) in \(m\)**, is
\[
 H_f(m)=\sum_{\substack{e\mid m\\(e,r)=1}}\mu(e)\,
          g_r(\log e/\log m),\qquad
 g_r(t)=f(t)-f(t+u_r).                                                   \tag{3}
\]
This simply separates the squarefree divisors containing the prime bit \(r\) from those not containing it. Since \((e,r)=1\), the condition \(e\mid m\) together with \(r\mid m\) is exactly \(re\mid m\), including on \(r^\nu\mid m\). No approximation by \(r\parallel m\) is made. For \(r\) beyond the support, \(g_r=f\) on \(t\ge0\). For \(r\) below support, \(g_r'(0)=f'(0)-f'(u_r)=-1-f'(u_r)\) with uniformly bounded \(C^2\) norm.

Apply (3) first to the **all-integer** \(q\) sum. Open the \(q\) divisor \(d\), restrict exact units on \(s,r,N\), and for the wide \(h\) first discard \(s\mid q\) at power-small absolute cost \(x^{.90+o(1)}\). (Those rows can be restored under the fixed opened masks at the same cost.) The actual CRT conditions \(d\mid q,\ re\mid m\) have one class modulo \(dre\) whenever \((d,e)=1\) and \((de,Nsr)=1\), with \(r\ne s\). If \(r=s\) on physical units then \(r\nmid m\), hence the row is empty. If \(r\mid N\) the row is also empty, and \(r\mid d\) or a common \(d,e\) prime would contradict the exact units. The \(r\)-shifted kernel in (3) has no effect on the \(.974\) total floor exponent or the uniform bounded variation of the physical weights in the preceding note. Its modeled bivariate harmonic sum is zero to arbitrary log reserve because \(h\) is flat, by exactly the same masked bivariate \(\mu/d\) product. The proof allows small \(r\): the mask \(F=Nsr\) is polynomial, the external harmonic mass \(\sum_{r\le x^B}\log r/r\ll L\), and all bounds on \(g_r,g_r'\) remain uniform. Thus the full \(q\)-integer sum against \(V_{\le B}\) is \(O_A(xL^{-A})\).

## 3. Remove the genuine \(q\)-prime column, including genuinely tiny tags

On actual prime \(q\), \(H_h(q)=1\). Use (3) and full-scale product BV on the true \(n=s q\) sequence for all \(re\le x^{B+.001+o(1)}\le x^{.490+o(1)}\), exactly as in the broad tag proof. The possible factorizations of a fixed modulus \(re\) now number at most \(\omega(re)\), a fixed log loss, not a power loss. The \(g_r\) and \(W_s\) physical weights admit the same product mesh with log-bounded variation; the raw moduli are reduced. The class model has exact factor \(1/(\phi(r)\phi(e))\). Here \(r=s\) can be removed at power-small cost and \(r=q\) is impossible; \(e\) cannot contain the macroscopic prime \(s\) or \(q\). The primes dividing \(N\) are kept excluded.

We need the first-order **finite** harmonic formula uniformly for the shifted, not necessarily affine, \(g_r\). For an even polynomial mask \(F\) and a smooth compact positive-side test \(g\) of bounded \(C^2\) norm, it is
\[
 (\log m)\sum_{(e,F)=1}\frac{\mu(e)}{\phi(e)}
      g(\log e/\log m)
 =-\mathfrak S(F)g'(0)
    + O_g\!\left(\mathfrak S(F)\frac{1+\log L}{L}\right).                \tag{4}
\]
Here and below “compact positive-side” means vanishing above the fixed positive cutoff, not vanishing at zero. To prove (4), for \(\Re z>0\) factor the series as
\[
 \sum_{(e,F)=1}\frac{\mu(e)}{\phi(e)e^z}
 =
 \frac{1}{\zeta(1+z)}\prod_{p\mid F}(1-p^{-1-z})^{-1}
     \prod_{p\nmid F}\left(1-\sum_{\ell\ge1}
                    \frac{p^{-\ell z}}{p^\ell(p-1)}\right).
\]
The last factor has an absolutely convergent coefficient sum with fixed positive Rankin margin \(d^\delta\) for \(\delta<1\). At \(z=0\) its value is \(\prod_{p\nmid F}[1-(p-1)^{-2}]\). Apply the finite shifted \(\mu/d\) estimate from [BilateralTrueTagCovariance](BilateralTrueTagCovariance.md), with shifts \(\log d\) from those coefficients. Its error \(O((F/\phi F)(1+\log L+\log d)/L^2)\) before multiplying by \(\log m\) follows directly by integrating the cumulative masked Möbius sum against \(g'\). The log moments of the absolutely convergent factor are bounded, and \(F/\phi F\asymp \mathfrak S(F)\), so this gives (4) with no uncontrolled dependence on \(F\).

At fixed physical \(n=sq\), (4) with \(F=Nr\) gives the principal coefficient
\[
 \frac{\mathfrak S(Nr)}{\log m}\,[1+f'(\log r/\log m)]
                      \frac{\log r}{\phi(r)}.                           \tag{5}
\]
If \(\log r/\log m\) is in the fixed affine neighborhood, the leading bracket is **exactly zero**. The error in (4) still sums to \(o(M_N)\) even across all \(r\), using the external logarithmic prime harmonic sum. Nonzero leading brackets require \(r\ge x^{\eta}\) for a fixed \(\eta>0\) determined by the affine neighborhood. Consequently replacing \(\mathfrak S(Nr)\) by \(\mathfrak S(N)\) there changes only a power-small amount, and omitting \(r\mid N\) is also power-small. This handles genuinely tiny divisors of \(N\) without charging their local singular-series ratio as \(1+o(1)\). Replacing \(\log m\) by \(L\) in the normalized variable and prefactor costs \(O_f(M_N/L)\). Ordinary PNT in the true \(s,q\) product, with prime harmonic sums for \(r\), now evaluates the true prime-\(q\) atom against \(V_{\le B}\) as
\[
 \left(J\int_0^B (1+f'(u))\,du+o(1)\right)M_N
     =\big(J[B+f(B)-1]+o(1)\big)M_N .
\]
The sign in (1) is the subtraction of this prime atom from the preceding all-integer zero. Proper prime-power corrections from the equivalent \(B_h C_f\) representation are uniformly power-small (as before), but the actual marked factors of **all composite rows** have already been included in (3). In particular neither bounded \(r\) nor small-power multiplicity is discarded in the tag expansion itself.

## 4. Exact scope of conservation

On a squarefree \(m\), \(V_{\le B}+V_{>B}=1\) exactly. On arbitrary \(m\) the weights lie in \([0,1]\) and \(0\le1-V_{\le B}-V_{>B}\le1\), supported on squareful \(m\). In the bilateral weighted upper for \(H_h H_f\), both kernels here are \(C_c^\infty\), so its small-factor argument applies to this fixed \(h,f\) with constants depending on the full kernels. For each fixed \(0<\kappa<.04\), rows with a prime \(\le x^\kappa\) on either leg have absolute weight \(O_{f,h}(\kappa M_N)+O(x^{.98})\). On the remaining rows a physical square divisor costs \(o_\kappa(M_N)\) by the square-divisor opening in that note. First take \(x\to\infty\) at fixed \(\kappa\), then let \(\kappa\downarrow0\). Thus even the nonsquarefree loss in the conservation identity is \(o(M_N)\), proving (2). This order does not claim constants uniform under shrinking the kernels.

A reason to keep this reformulation is that a wide \(h=1\) on \([0,.39]\) and supported up to \(.400\) is allowed: it makes \(H_h(q)=0\) exactly on composite \(q\) with a prime \(p>q^{.61}\), since only divisors of \(q/p>1\) can occur and their weights are all 1. At the same time (2) localizes the reflected leg to a genuine prime \(r>x^{.489}\). This exact support saving and the one-leg conservation are not a bound for the surviving large-tag signed operator. Its negative target in (2) must still be met, and the small-tag positive mass cannot be forgotten when interpreting the earlier \(.1051 M_N\) intermediate threshold.
