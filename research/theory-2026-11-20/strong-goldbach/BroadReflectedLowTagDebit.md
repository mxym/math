# A broad negative reflected-prime tag term in the actual bilateral ledger

The short-kernel ledger allows a substantial **signed** extraction without a \(q\)-side tag on the low reflected-prime band. It can be combined with an exactly zero tag expression on a disjoint upper band. The resulting remaining required upper bound is explicit; it is not proved here.

## 1. Physical identity and statement

Keep \(N=2x\), \(L=\log x\), \(M_N=\mathfrak S(N)x/(2L)\), actual prime \(s\in(x^{.10},x^{.14})\), \(n=sq\in(x/2,x]\), \(m=N-n\), \((n,N)=1\), and \(W_s(q)=(1-t)(1-2t)^2,\ t=\log s/\log n\). Write \(J=\log(7/5)-.160+.0192\). Take the exact affine/flat kernels \(f,h\) supported in \([-.001,.001]\) from [BalancedLargeTagTaper](BalancedLargeTagTaper.md); \(H_g(y)=\sum_{d\mid y}\mu(d)g(\log d/\log y)\), and put \(X_h(s,q)=W_s(q)(\log m)H_h(q)H_f(m)\). Its exact whole centered identity is
\[
 E_N=\sum_{s,q;\ q,m\ {\rm composite}} X_h(s,q)+O_A(xL^{-A})
\]
for every fixed \(A\), with the literal original \(E_N\). Define the actual distinct-prime mark weights
\[
 V_0(m)=\sum_{\substack{r\mid m,\ r\ {\rm prime}\\ x^{.003}<r<x^{.489}}}
                      \frac{\log r}{\log m},
 \qquad
 V_1(m)=\sum_{\substack{r\mid m,\ r\ {\rm prime}\\ x^{.489}\le r<x^{.506}}}
                      \frac{\log r}{\log m}.
\]
The bands are disjoint, and \(0\le V_0+V_1\le1\) on every physical row, not just squarefree ones. Then
\[
 \sum_{s,q;\ q,m\ {\rm composite}} X_h(s,q) V_0(m)
       = -(.486 J+o(1))M_N.                                             \tag{1}
\]
The same evaluation for \(V_0\) alone holds with any fixed smooth \(h\) supported up to \(.400\) on the positive side and exactly flat near zero.

Together with the exact \(U_S(q)V_1(m)\) null from the balanced large-tag proof (same short \(h,f\); changing the \(r\) interval only restricts its allowed source), this gives
\[
 E_N =-(.486J+o(1))M_N+
        \sum_{s,q;\ q,m\ {\rm composite}} X_h(s,q)[1-V_0(m)-U_S(q)V_1(m)] .
                                                                         \tag{2}
\]
Here \(U_S\) is exactly the balanced large-tag \(q\) weight, not an independently replaced model; the bracket is nonnegative because \(U_S\le1\) and the reflected bands are disjoint. The original sufficient upper threshold \(.010M_N\) on \(E_N\) corresponds to \((.010+.486J)M_N\) on the remaining signed sum, approximately \(.10510 M_N\) (with a fixed strict margin if used to deduce eventual positivity). This does not import the wide-kernel debit reserve or re-use the same negative mass on overlapping charts.

## 2. The complete integer sum with the low tag is zero

Every marked \(m\) is composite. First allow *all* integer \(q\), and include the factor \(H_h(q)\) as part of \(X_h\). Open a genuine marked \(r\mid m\), and the two short score divisors \(d\mid q,\ e\mid m\). They satisfy \(d\le q^{.001}\) (or \(d\le q^{.400}\) in the stated extension), \(e\le m^{.001}\), \(r>x^{.003}>e\). Since \(m+sq=N\) with physical units, \(r,e\) are prime to \(N,s,d\), except that \(s=r\) is an empty physical row. For the extended \(h\)-support, first remove the physical rows \(s\mid q\); their absolute cost is \(x^{.90+o(1)}\) since at fixed \(s\) there are \(O(x/s^2+1)\), and divisor weights are \(x^{o(1)}\). The short \(h\) already excludes \(s\) from \(d\). We may then impose the exact restrictions \((de,Nsr)=1,\ (d,e)=1\): \(s\nmid e\) by size, and if \(r\mid d\), \(r\) would divide both \(q\) and \(m\). Any deleted rows can be reinserted when calculating the geometric main with these fixed divisor masks at the same power-small cost. The unit masks on \(r,s\) are kept. Repeated \(r\)'s in \(m\) need no deletion or multiplicity division: \(r\) is counted once per actual distinct prime tag, and no active divisor \(e\) contains it.

For each such tuple, \(d\mid q\), \(r e\mid N-sq\) define one CRT class modulo \(d r e\); demanding \((q,N)=1\) gives prefix density \(\phi(N)/(N d r e)\) and error \(O(\tau(N))\). Open the physical interval in \(q\), with smooth weight and bounded variation; multiplication by \(\log r\) is the exact cancellation of the \(\log m\) in \(X_h\) against the tag normalization. For the extended \(.400\) support the unweighted floor-search exponent is at most
\(.140+.400(1-.140)+.001+.489=.974\), and for the short support smaller. Divisor multiplicities and logs lose only \(x^{o(1)}\). The small divisor pair in its geometric principal is then
\[
 \sum_{\substack{(d,e)=1\\ (de,Nsr)=1}}
     \frac{\mu(d)\mu(e)}{de}
          h(\log d/\log q) f(\log e/\log m).
\]
It is \(O_A(L^{-A})\) for every \(A\): use the bivariate absolutely Rankin-convergent convolution from [BilateralTrueTagCovariance](BilateralTrueTagCovariance.md), and the exact flat neighborhood of \(h\) to apply the masked \(\mu/d\) estimates in the zero-mode section of the balanced large-tag proof. These apply to the true moving denominators here without freezing the \(r\) label. The factors omitted from the harmonic sum due to \(r\mid N\) or \(s=r\) are kept as exclusions, not assigned any false zero. The remaining external masses \(\sum_s 1/s\) and \(\sum_r \log r/r\) preserve arbitrary log reserve. Thus the *full* low-tag sum of \(X_h\), including prime \(q\), vanishes to arbitrary log reserve.

## 3. Remove the true prime \(q\) atom

On every true prime \(q\) in the central interval, \(H_h(q)=1\) exactly. The contribution to subtract is therefore
\[
 \sum_{\substack{r\ {\rm prime}\\x^{.003}<r<x^{.489}}}
  \log r\sum_{\substack{e\le(1.5x)^{.001}\\(e,Nr)=1}}\mu(e)
    \sum_{\substack{s,q\ {\rm prime}\\ n=sq\equiv N\bmod re\\
                       n\in(x/2,x],\ (n,N)=1}}
          W_s(q) f(\log e/\log(N-n)),                                  \tag{3}
\]
where as always tags with \(r\mid N\) are omitted. The two-factor [full-scale product BV](FullScaleConvolutionBV.md) applies at the actual scale \(x\) of \(n=sq\), with the true prime \(q\) as the long SW factor, and moduli \(re\le x^{.490+o(1)}<x^{1/2-\delta}\) for a fixed \(\delta>0\). Each modulus has at most one such \(r\) since \(e<x^{.003}\), so coefficients carry only fixed log powers, and source maximal-prefix or the product-mesh argument there handles the bounded variation in \(e,n\). This step is not prime BV at the shorter \(q\)-scale.

The local main is the reduced factor \(1/\phi(re)\), with \((n,re)=1\) in the unrestricted source principal. The \(e\) mask is automatic at the macroscopic primes \(s,q\); \(r=q\) is impossible by their sizes. The exceptional diagonal \(r=s\) has no actual rows and must be omitted in the model; its absolute model cost is power-small, from \(\sum_{s>x^{.10}}\log s/s^2\) after summing \(q\) up to \(x/s\) and opening the harmonic \(e\)-sum if needed. Likewise the polynomial prime factors of \(N\) that are omitted from any of the label sums have power-small cost (there are boundedly many in any prescribed fixed positive-power range). Now at fixed \(r,n\), since \(m\asymp x\) and \(f(t)=1-t\) exactly near zero, the finite \(\mu/\phi\) Euler identity gives
\[
 (\log m)\sum_{(e,Nr)=1}\frac{\mu(e)}{\phi(e)}
                  f(\log e/\log m)=\mathfrak S(Nr)+O_A(L^{-A}).
\]
Here \(\phi(re)=\phi(r)\phi(e)\) on the true allowed rows. Uniformly for these polynomially large primes \(r\nmid N\), \(\mathfrak S(Nr)=\mathfrak S(N)(1+O(1/r))\). The prime reciprocal-log sum gives
\[
 \sum_{x^{.003}<r<x^{.489}} \frac{\log r}{r-1}=(.486+o(1))L.
\]
Since \(\log m=L+O(1)\), (3) is
\[
 (.486+o(1))\mathfrak S(N)
     \sum_{\substack{s,q\ {\rm prime}\\x/2<sq\le x}} W_s(q)
  =(.486 J+o(1))M_N.
\]
In the last equality the ordinary PNT on the prime \(q\)-interval at fixed \(s\), then the prime harmonic sum on \(s\), give
\(J=\int_{.1}^{.14}W(t)dt/[t(1-t)]\); omitting the target units changes this only by a power-small error. The sign in (1) is **negative** because this actual \(q\)-prime atom is subtracted from the all-integer geometric zero. Proper prime powers \(q\) or \(m\) are already power-small in the exact whole identity and are still so under all mark weights here (which lie in \([0,1]\)). There is no exclusion of any true prime mark multiplicity from a composite, and no prime-prime or pointwise remainder estimate is asserted.

## 4. What this controls

Equations (1)–(2) isolate a uniformly negative **actual** part of the same short-kernel signed criterion, even without a \(q\)-side tag. Unlike a smaller shape-specific balance band it applies simultaneously to all quotient profiles with a reflected mark in the stated broad range. The new residual includes both larger reflected prime factors and reflected small prime factors below the lower tag boundary, so this does not establish the needed upper limit on it. In particular it does not permit treating every omitted small mark as a negligible term with constants uniform as the kernel support shrinks.
