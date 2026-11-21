# Reverse completion removes a large-reflected-prime shoulder of the actual double-high ledger

In the exact short-kernel double-high operator of [DualPrimeLogConservation](DualPrimeLogConservation.md), one can remove additional true prime tags well beyond the \(r<x^{.506}\) forward completion window of [BalancedLargeTagTaper](BalancedLargeTagTaper.md). Complete the **reflected** free cofactor instead. A partial interval Cauchy bound keeps the genuine prime \(s\) in the phase, now with *different moduli* \(s p d\) and \(s'p d\). The result removes a signed, equation-sensitive part of the actual remaining operator; it does not upper-bound the rest.

## 1. Exact chart

Keep all the physical conventions, unit masks, \(W_s(q)\), \(X_h(s,q)\), and \(M_N\) of those notes. Take the short \(h,f\) kernels supported on \([-.001,.001]\), \(h=1\) and \(f(t)=1-t\) near zero, with the \(a=.357\) version of dual conservation. The true labels \(p\mid q,\ r\mid m=N-sq\) in its actual residual satisfy \(p>x^{.357},r>x^{.489}\). Let \(\mathcal C\) be the disjoint union of the two exponent charts
\[
\begin{aligned}
 .357<\log_x p<.387,\qquad &.530<\log_x r\le.600,\\
 .357<\log_x p<.367,\qquad &.600<\log_x r<.629.
\end{aligned}
\]
Endpoints can also be omitted, with those literal subcharts unchanged. Both allow the entire \(.10<\log_x s<.14\). Then at every even target the signed contribution
\[
 \sum_{\substack{s,q;\, q,m\ {\rm composite}\\
                 p\mid q,\ r\mid m\ {\rm prime},\ (\log_x p,\log_x r)\in\mathcal C}}
 X_h(s,q)\frac{\log p}{\log q}\frac{\log r}{\log m}
             =O_A(xL^{-A})                                             \tag{1}
\]
for each fixed \(A\). The two displayed proper tags themselves force the legs composite, \(p\ne r\), and \(r>\sqrt m\) for large \(x\). The \(p\)-label is still counted with its literal log weight if there are several eligible labels. The statement is about signed removal, not a small positive-part upper.

These charts include true supercritical \(s p r>x\), not just elementary CRT. For example at interior exponents \(s=.120,p=.365,r=.570\), actual semiprime \(q\) and semiprime \(m\) have respective other prime exponents \(.515,.430\), and both short scores equal 1. This profile has genuine positive dyadic occupation by ordinary PNT on the last factors on each independently chosen \(n,m\) product interval, with all bands disjoint, as in the forward note. The fixed-target result (1) does not presume a lower bound for that occupation at an individual \(N\).

## 2. The actual reversed residue

Open the short divisor \(d\mid q\) from \(H_h\) and \(e\mid m\) from \(H_f\); both are \(\le x^{.001+o(1)}\). Neither contains \(s,p,r\) by size. The true masks are \((de,N s p r)=1\), \((d,e)=1\), and \((s p r,N)=1\). No separate requirement that the whole \(q\) or \(m\) is squarefree is used: its large prime labels are outside the active divisors even if repeated. On writing \(q=p d u,\ m=r e v\), the remaining target-unit condition is \((v,N)=1\), since both legs are simultaneously units. Expand it with \(g\mid N\) and put \(v=g w\); the terms \(g>x^{.0001}\) cost \(x^{1-.0001+o(1)}\) absolutely by \(g\mid m\), \(O(x/g+1)\) actual \(m\)'s, and divisor bounds at the true \(m,n\). The residue for the reflected free \(w\) is now
\[
 w\equiv N\overline{r e g}\pmod{s p d}.                                \tag{2}
\]
It is reduced. The variable modulus \(s p d\) is not replaced by \(p d\).

Use the same central smoothing and dyadic independent boxes as in BalancedLargeTagTaper. Endpoint strips of log-power relative width cost arbitrary log reserve by short-interval divisor moments; all physical and opened weights at one \(n,m\) are bounded by fixed divisor powers. Write
\[
 S=x^\sigma,\ A=x^\alpha,\ B=x^\beta,\ D=x^\delta,\ E=x^\epsilon,\ 
 g=x^\gamma,\qquad \zeta=.0002
\]
for the actual dyad scales of \(s,p,r,d,e,g\) (with \(o(1)\) in exponents at endpoints). For fixed outer \(p,d,e,g\), Poisson in (2) uses \(V_0=x/(r e g)\), with frequency cutoff
\[
 T\asymp (S A D B E g/x)x^\zeta,\qquad
 t=\log_x T=\sigma+\alpha+\beta+\delta+\epsilon+\gamma-1+\zeta+o(1)
\]
when nonempty. Omitted frequencies cost a power savings by repeated integration by parts of the log-smooth physical weight. The average-zero modes will be evaluated separately below.

Explicitly separate the smooth weight first in \(\log(s/S)\) on its fixed compact dyadic chart, now treating \(p,d,e,g\) as fixed. After Poisson, on each signed frequency dyad separate the amplitude \(\widehat\Phi(k V_0/(s p d))\) by a Fourier expansion in \(\log(|k| V_0/(s p d))\) on its compact logarithmic dyad; it factors into weights in \(k,r,s\) because \(V_0=x/(r e g)\). As in the forward proof, two derivatives in the compact separation variables give polylogarithmic \(L^1\) norm. Repeated integration by parts in the smooth physical variable controls both the tail and the fixed logarithmic derivatives uniformly at large arguments. The factor \(\log r\) and the bounded \(r\)-prime coefficient stay on the actual \(r\) axis, and \(V_0/(s p d)\) separates into inverse \(r\) and \(s\) dyad factors. Thus after taking out log powers and this Poisson size only genuinely independent \(r,s,k\) coefficients remain, with the actual \(s\)-prime label retained.

## 3. An incomplete second moment with two different \(s\)-moduli

For \(P=p d\), the nonzero sum in a box is bounded by controlling
\[
 \sum_{r\in I} \eta_r
 \sum_{\substack{s\sim S\ {\rm prime},\ 0<|k|\le T\\(r,sP)=1}}
       \lambda_s\omega_k\, e_{sP}(kN\overline{r e g})
\]
with 1-bounded separated coefficients and \(I\) the actual interval of length \(O(B)\). Drop the prime restriction on \(r\) **only in the interval second moment**, retaining each individual unit indicator. The diagonal costs \(O(BST)\).

For off-diagonal pairs with \(s\ne s'\), \((s,s',P)=1\) and the combined phase on common units is exactly
\[
 e_{P s s'}\big(N\overline{r e g}\,(k s'-k's)\big).
\]
There is no approximation of the \(r\)-inverse denominator here. For \(s=s'\) the denominator stays \(P s\) and numerator is \(N(k-k')\overline{e g}\). In the two charts \(2T<\min s\) by a fixed power margin, since
\(\alpha+\beta+\delta+\epsilon+\gamma+\zeta\le.9983+o(1)\).
Also \(4ST<p\) by a fixed power margin since \(2\sigma+\beta+\delta+\epsilon+\gamma+\zeta\le.9113+o(1)\).
Hence the nonzero off-diagonal numerator is a unit modulo \(p\): an equality modulo \(p\) in the unequal-\(s\) case would be the equality of the integers \(k s'\) and \(k's\), impossible for distinct primes \(s,s'\) and \(0<|k|,|k'|<\min s\). In the equal-\(s\) case the nonzero \(k-k'\) is shorter than both \(s,p\). The unequal-\(s\) numerator is also a unit at \(s,s'\), since \(k,k'\) are nonzero and shorter than those primes. All these primes are units at \(N,e,g\). At \(d\) allow arbitrary gcd, bounded by \(d\) exactly.

It follows from interval completion and the [prime Weil estimate](https://doi.org/10.1073/pnas.34.5.204) on the coprime factors of the squarefree modulus that the incomplete period costs at most \(x^{o(1)}\sqrt A\,D S\) for either orientation. Indeed the modulus is at most \(p d s s'\), and the numerator gcd is at most \(d\). If the interval is longer than the modulus, each full period is a Ramanujan sum of absolute size at most \(d\); all of them add \(O(B/(A S)+D)\) in the worst equal-\(s\) case. This is covered by the incomplete-period bound, since \(\beta-\alpha-\sigma\le.629-.357-.100=.172<.357/2+.100\). For unequal \(s,s'\) the full-period term is smaller. This accounting retains all common unit masks after Cauchy.

Thus the trilinear sum is at most
\[
 x^{o(1)}\big[B\sqrt{ST}+\sqrt B\,ST\,A^{1/4}D^{1/2}S^{1/2}\big].
\]
Multiply by \(x/(S A D B E g)\) and pay at most \(A D E\) for \(p,d,e\). The resulting exponent bounds are
\[
 1+\tfrac12(\alpha+\beta+\delta+\epsilon-1-\gamma+\zeta),\qquad
 \tfrac54\alpha+\tfrac12\beta+\tfrac32\sigma+\tfrac32\delta+\epsilon+\zeta.
\]
They are respectively at most \(.9946+o(1),.99645+o(1)\) in the first chart, and \(.9991+o(1),.98595+o(1)\) in the second. All \(g\mid N\), dyadic choices, and separations cost \(x^{o(1)}\). This gives uniform power saving for the entire nonzero range; in particular one cannot simply estimate it as if the two original moduli were the same.

## 4. Exact zero frequency and what is removed

The zero-frequency principal in (2) is the true geometric density \(1/(s p d\,r e g)\) in \(m\), integrated against the identical physical weights. Extending \(g\) to all divisors of \(N\) costs \(x^{1-.0001+o(1)}\) in this model as well, and supplies exactly \(\phi(N)/N\). For each real \(s,p,r\) the remaining short two-divisor factor is
\[
 \sum_{\substack{(d,e)=1\\(de,Nspr)=1}}
       \frac{\mu(d)\mu(e)}{de}
      h(\log d/\log q)\,f(\log e/\log m).
\]
As in the forward proof's zero-mode argument, the absolutely Rankin-convergent coupling Euler factor separates two coprime \(\mu/d\) sums; the exactly flat \(h\) makes its half arbitrary-log small even after the small Euler shifts. This is uniform in the actual \(q,m\) in the physical integral. The labels \(s,p,r\) are summed harmonically and have only fixed log powers; no additional distribution theorem is needed for the zero-mode cancellation. All constants therefore fit (1).

For the short \(a=.357\) variant of dual conservation, (1) can be subtracted directly from the actual double-high row. It is disjoint from the earlier forward taper restricted to \(r<x^{.506}\); if also subtracting a subcritical determinant region, partition first to avoid double counting. No offset is taken from the broad \(h\)-kernel variant, which has different divisor lengths. The exact \(.010 M_N\) sufficient cap still needs a genuine signed proof on the remaining union of high-high profiles.

## 5. Union of the two completion rails

The estimates apply equally to any fixed finite disjoint collection of independent exponent boxes obeying the relevant strict margins, with the same short kernels. In the true high-high domain \(\alpha>.357,\ \beta>.489,\ .10<\sigma<.14\), for example require \(\alpha+\beta<.997\) throughout each box. Then all the nonfrequency wrap conditions and interval-full-period estimates in either direction have fixed power reserve (the short divisor and unit cutoffs are the same). Ignoring the \(o(1)\) from dyadic endpoints, the sufficient two alternative off-diagonal rails on these boxes are
\[
 \begin{aligned}
 &\sigma+\tfrac12\alpha+\tfrac54\beta+.0027<1
                       &&\text{(complete the \(q\)-cofactor)},\\
 &\tfrac32\sigma+\tfrac54\alpha+\tfrac12\beta+.0027<1
                       &&\text{(complete the \(m\)-cofactor)}.
 \end{aligned}
\]
The first adds \(\delta+3\epsilon/2+\zeta\), the second \(3\delta/2+\epsilon+\zeta\), both at most .0027. Fixed boxes lying in both are used once. In particular, if the sum of prime exponents is \(w=\alpha+\beta\), the larger-possible value of the smaller uncorrected rail is at most \(1.25\sigma+.875w\), by intersecting the two affine functions of \(\alpha\). Thus every fixed eligible box contained in \(1.25\sigma+.875w+.0027<1\) has at least one available orientation, after subdivision where necessary and preserving strict margins. This is not a claim that their full rectangular union covers the remaining profiles. For example at \((\sigma,\alpha,\beta)=(.139,.450,.545)\) both uncorrected rails already exceed 1; the exact determinant is supercritical, and the elementary union leaves this profile and all sufficiently nearby profiles untouched. Such pairs need a different arithmetic bound, not another choice of orientation within this argument.

## 6. The improved dual cutoffs and a disjoint literal union

The same short \(f,h\) that are \(C_c^\infty\) at their support endpoint allow the sharper complete dual cutoffs \(a=.359,\ B=.499\). The \(q\)-side modulus exponent in dual conservation is \(.140+.860(.001)+.359=.49986\); fixing the short-\(v\) split at \(x^{.0001}\) keeps its single-prime BV bound below the square root exponent .49995. Both factors in the long-product branch remain polynomially long. The \(p\)-integral still spans the entire \(h'\) support. The geometric model for the \(m\)-tag part has the floor exponent at most .984, even with the wider \(h\) if considered **only** for that one-leg projection.

For the \(m\)-tag true \(q\)-prime column at \(B=.499\), use generalized BV only through \(x^{1/2}/L^C\) with \(C\) chosen for the desired reserve. On a potentially omitted modulus \(r e>x^{1/2}/L^C\), the bounds \(r\le x^{.499}\) and \(e\le m^{.001}\) force
\[
 e\ge x^{.001}/L^C,\qquad r\gg x^{.499}/L^C .
\]
The \(r\)-shift in the opened bit test is therefore identically zero. Wherever the unshifted \(f(\log e/\log m)\) is nonzero, its argument is within \(O_C(\log L/L)\) of .001. All derivatives of \(f\) vanish there, so Taylor bounds give an arbitrary power of \(\log L/L\). In the actual discarded sum the remaining absolute factors at each \(n\) are at most fixed powers of \(L,\tau(n),\tau(m)\). In the discarded centered model the absolute harmonic sums over \(r,e\), including all labelings of their product, cost only log powers as well. Hence choosing the Taylor order after \(C\) makes both omitted terms \(O_A(xL^{-A})\). This justifies the original reflected harmonic evaluation at the exact endpoint \(B=.499\), rather than using a theorem at arbitrary moduli of size \(x^{1/2}\). The sharp raised reflected term \(+.501 J M_N\) is exactly canceled by the dual negative term with the same new \(B\). Thus the remaining \(.010 M_N\) criterion is still on the literal two-high labels, now \(p>x^{.359},r>x^{.499}\).

Three independent forward strips also fit, as observed in the companion numerical audit. All prime tags below are subject to these two raised lower bounds. Use the actual dyadic \(S<s\le2S\).
\[
\begin{array}{c|c|c}
 \text{allowed }\log_x r & \text{additional }p\text{-cut}
       &\text{orientation}\\ \hline
 (.499,.5095] &p<x^{.010}\sqrt{x/(2S)}&\text{forward}\\
 (.5095,.525] & p\le x^{.400}&\text{forward}\\
 (.525,.535]  & p\le x^{.375}&\text{forward}\\
 (.530,.535]  & x^{.375}<p<x^{.387}&\text{reverse}\\
 (.535,.600]  & p<x^{.387}&\text{reverse}\\
 (.600,.629)  & p<x^{.367}&\text{reverse}.
\end{array}
\]
The first three follow exactly from the forward proof. Their off-diagonal ceilings including the explicit .0027 allowance are \(.999575,.998950,.998950\); the diagonal ceilings are \(.98585,.96360,.95610\). The \(T<s\) and \(ST<r\) margins are strict from \(\alpha+\beta+.0023<1\) and \(\alpha+2\sigma+.0023<1\), and all interval-period allowances are already covered. The last three are the literal independent portions of the reverse charts not already used by the forward strips. Row overlaps are therefore avoided without subtracting any true tag twice. These masks determine a nonnegative remaining tag measure, not the sign of its actual weighted sum. The elementary subcritical determinant null \(s p r\le x^{.997}\), if also used, can be intersected with the complement of the six masks: count the true triples by the divisor bound for integers \(s p r\le x^{.997}\) and pay the two additional short divisors in the geometric floor error, preserving .001 of power reserve. Neither orientation estimates the hard neighborhood exhibited in §5.
