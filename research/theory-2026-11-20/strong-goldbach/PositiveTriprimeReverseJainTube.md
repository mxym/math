# A genuine high reverse block of the positive triprime complement

Use the original true semiprime row \(N=2x,\ L=\log x,\ n=sq\in(x/2,x],\ m=N-n\), with \(s\) prime, \(x^{.10}<s<x^{.14}\), and physical unit condition \((n,N)=1\). The functions \(W_s(q)\) and \(C(m)\) have exactly the definitions of [ActualNegativeThreeMarkReserve.md](ActualNegativeThreeMarkReserve.md). In the reverse Vaughan opened row \(q\) is a positive integer; write
\[
 q=rkh,\qquad r>U_q=x^{.070},\quad k>V_q=x^{.010},
 \qquad A=srk.
\]
The product cut \(rk>x^{.080}\) is automatic here. The physical reverse coefficient is \(\mu(r)\Lambda(k)\) with a free \(h\) having weight \(1\). In particular \(s,r,k,h\) are not all asserted prime.

Here is an application of [Jain's Hexagon preprint, 2611.00530v1, Proposition 2](https://hexagonmath.org/pdf/2611.00530v1), not of its smooth-number theorem. Let \(C_*\) be its absolute constant. Fix \(0<\nu<.01\) and set, for \(\rho=\log_x A\),
\[
 a(\rho)=\frac{4\rho-7/4}{3},\qquad
 b(\rho)=\rho+\lambda-a(\rho),\qquad c(\rho)=1-\rho-\lambda,\qquad
 0<\lambda<\frac{\nu}{100(C_*+1)} .
 \tag{1}
\]
Choose \(w>0\) smaller than \(\lambda/100\). For genuine distinct primes \(p_1,p_2,p_3\) in the indicated order of size, assume
\[
  m=p_1p_2p_3,\quad m\in[x,3x/2),\quad
  .600<\rho<5/8-\nu,\quad
  |\log_xp_1-a(\rho)|<w,\quad
  |\log_xp_2-b(\rho)|<w .
 \tag{2}
\]
The third exponent is \(c(\rho)+O(w+1/L)\) because the product is central. Throughout this support all three factors are below \(x^{.41}<U\), while all pairs are above \(x^{.59}>\sqrt x\). Thus the literal original \(C(m)=+\log m\); this is in the **positive physical reflected complement**, not in the earlier negative marked family.

Let \(\Phi(\rho,u,v)\) be any fixed smooth bounded test supported in the open profile constraints (2), with \(u=\log_xp_1,v=\log_xp_2\), for example a product of independent bumps in \(\rho,\ (u-a(\rho))/w,\ (v-b(\rho))/w\). For any fixed \(D>0\), uniformly for each even \(N\), the actual signed reverse block is
\[
 \sum_{\substack{p_1p_2p_3+srkh=N,\ p_i,s\ {\rm prime}\\
       m\in[x,3x/2),\ (m,N)=1,\ r>U_q,\ k>V_q}}
   \Phi(\log_x A,\log_x p_1,\log_x p_2)\,
   C(m)\,\frac{W_s(rkh)}{\log(rkh)}\,\mu(r)\Lambda(k)
          =O_{D,\Phi,\nu}(xL^{-D}).
 \tag{3}
\]
The \(s\)-band from the first paragraph is understood. Every \(\rho\) in any fixed compact subinterval of \((.600,5/8-\nu)\) is allowed in a nonempty positive-width chart. The claim is a coupled exponent tube, **not** a statement for arbitrary positive triprime exponents at a given \(\rho\), nor a bound on the whole positive triprime sum. It uses the cited new preprint estimate as stated; neither current preprint is asserted to have been peer reviewed.

## 1. Independent source and strict rails

For fixed \(s,r,k\) the actual equation is the progression \(m\equiv N\bmod A\). The appropriate remainder \(h=(N-m)/A\) is a positive integer with no additional arithmetic restriction. Nonunit \(A\) sharing a prime with \(N\) gives no actual row by the physical masks. The full source is the product of the **three independent, genuine prime factors of \(m\)**, not a smooth-number density, and its scale is comparable to \(x\). In the source proposition take \(a_1=N,\ a_2=1\), and let the logarithmic sizes of its \((N_{\mathrm{slot}},L_{\mathrm{slot}},M_{\mathrm{slot}},R)\) be \((a,b,c,\rho)\).

To check the more delicate constraints, put \(d_0=a-(2\rho-1)=2(5/8-\rho)/3\ge2\nu/3\). At the indicated centers the exact margin calculations are
\[
\begin{split}
 a+b-\rho&=\lambda,\qquad
 c-b=d_0-2\lambda,\qquad
 2a\le .5-\tfrac83\nu,\\
 2a+3b-1-\rho&=-d_0+3\lambda,\\
 C_*(a+b-\rho)+a+.5-2b
   &=C_*\lambda-2(5/8-\rho)-2\lambda .
\end{split}
 \tag{4}
\]
All give strict margins, and \(a+b<2/3\), \(c<\rho\), \(a>0\) hold with strict fixed margins as well. To account for the possibly large \(C_*\), take the profile thickness \(w\) (if necessary) below \(\lambda/[100(C_*+1)]\), then take the proposition parameter \(\kappa\) sufficiently small in terms of \(\lambda,\nu,w\). Thus its hypotheses \(N_{\rm slot}\ge x^\kappa,\ N_{\rm slot}L_{\rm slot}\le x^{2/3-5\kappa},\ L_{\rm slot}\le x^{-\kappa}M_{\rm slot},\ M_{\rm slot}\le R\le x^{-\kappa}N_{\rm slot}L_{\rm slot}\), and the short-square, diagonal and complementary-divisor rails all fit. Actual dyadic normalizations and \(m/x\in[1,3/2)\) change exponents by \(O(1/L)\) only. The bound \(N=2x\le X^{1+\delta}\) holds at every local source scale \(X\asymp x\).

For an explicit contrast, the different [arXiv preprint 2611.21136v1, Proposition 3, (3.1)](https://arxiv.org/html/2611.21136v1#S3.SS1) would require \(7a+4b+\theta<2+2\rho\) at the same large residue with \(\theta=7/32\). At our centers the excess is \(6\rho-3.53125+4\lambda\ge .06875\). Since \(a<b<c\), assigning the smallest genuine exponent to the coefficient \(7\) and the next smallest to \(4\) already minimizes the left side across permutations of the three slots. That theorem does not cover this tube by regrouping these three actual prime slots. Its smooth-number level \(153/256\) is a different application.

One can cover the compact profile support by finitely many exponent boxes, including intervals of \(\rho\), sufficiently fine that the strict rails hold over their entire independent closures. Refine source sizes dyadically and use positive or signed fixed smooth partitions to separate \(\Phi\) in its three log coordinates by Fourier inversion. The normalization costs only fixed constants depending on the test and margins; Fourier factors in each prime coordinate have logarithmic derivatives bounded by a fixed log power after cutting each Fourier variable at \(L^B\). Arbitrarily high smoothness makes the tail log-small after the usual divisor-moment bound on physical terms and harmonic modulus sum on the principal. The exact test at fixed \(m,s\) is \(\log m\,W_s((N-m)/s)/\log((N-m)/s)\); Taylor in \(\log((N-m)/x)=O(1)\) separates its dependence on \(\log s\) into fixed log powers and smooth \(m/x\)-factors to any prescribed precision, as in [TrueSemiprimeReverseDispersion.md](TrueSemiprimeReverseDispersion.md). Impose the sharp central product by fine relative \(L^{-B}\) Cartesian meshes; boundary errors occupy \(O(xL^{-B})\) physical integers with the usual divisor moments. Retained local boxes all have \(m<1.6x<N\), important for the divisor-moment step below. Thus the analytic use of the proposition concerns genuinely independent input coefficients, not Möbius on an arbitrary unfactored quotient.

## 2. Centering large and small characters before weighting the modulus

At each fixed box and separated term apply Jain's Proposition 2 first with a **polylogarithmic** conductor cutoff \(D_0=L^F\). Its high-character error summed absolutely over the eligible \(A\) can be \(O_B(xL^{-B})\) for any fixed \(B\) by increasing \(F\). The small nonprincipal characters discarded in that proposition are log-small after the same absolute summation: one actual prime slot has ordinary SW with arbitrary log reserve and ordinary partial summation for the retained Fourier coefficients. Its auxiliary \((p,A)=1\) restriction deletes only \(O(L)\) legitimate prime values; every source slot is polynomially long. The other two slots are bounded in \(L^1\), the number of induced characters of conductors up to \(D_0\) is \(O(D_0^2)\), and \(\sum_A1/\phi(A)\ll L^C\). This yields log-small discrepancy against the **ordinary reduced mean** \(\phi(A)^{-1}\sum_{(m,A)=1}\) with no remaining small-character weight.

To attach the actual outer weights, do not multiply the absolute error by a pointwise \(x^{o(1)}\) divisor bound. Write \(\Delta_A\) for that *ordinary* discrepancy. For every fixed \(j\),
\[
 \sum_{A}\tau(A)^{2j}|\Delta_A|\ll xL^C.
\]
Indeed the progression part is bounded by
\(\sum_{m\asymp x}\tau(m)^C\sum_{A\mid N-m}\tau(A)^{2j}\ll xL^C\)
using divisor moments on the actual \(m,N-m\) ranges, with no zero difference. The mean part uses \(\sum_A\tau(A)^{2j}/\phi(A)\ll L^C\). Cauchy between this bound and the unweighted log saving preserves every requested logarithmic reserve. It covers the literal weighted decompositions \(A=srk\): summed over those decompositions, \(|\mu(r)\Lambda(k)|\) and any separated bounded test cost at most \(L^C\tau(A)^C\). This applies after restoring the finite exponent boxes and product cuts using their already stated reserves. It does not assume an unweighted large-sieve asymptotic for high-conductor Möbius on \(q\).

## 3. The actual signed principal is zero to log precision

In the ordinary reduced mean fix \(m,p_1,p_2,p_3,s,k\), requiring \((s k,Nm)=1\); if not, the mean is exactly zero. The exact test \(W_s/\log q\) is independent of \(r\) at fixed \(m,s\). The selected \(r\)-weight \(\Phi(\log_x(s r k),u,v)\) has bounded total variation, and all endpoints retained in \(r\) are above \(U_q\). The signed harmonic sum to evaluate is
\[
 \sum_{\substack{r>U_q\\(r,Nm)=1}}
          \frac{\mu(r)\Phi(\log_x(s r k),u,v)}{\phi(s k r)}.
\]
A finite interval may also be retained. Factor \(1/\phi(s k)\) and use the exact remaining local ratio \(\prod_{p\mid(s k,r)}(1-1/p)\). Expand it over \(d\mid\operatorname{rad}(s k)\), with coefficient \(\mu(d)/d\): there are at most four terms. When \(d\le x^{.035}\), write \(r=d r'\), retain the true squarefree \((r',d)=1\) mask, and apply the finite coprime \(\mu/\phi\) constant moment in [UnmarkedSemiprimeWholeTypeI.md](UnmarkedSemiprimeWholeTypeI.md), equation (11), with mask \(dNm\) at the polynomial endpoints of \(r'\). Ordinary partial summation treats the smooth \(\rho\)-test. If \(d>x^{.035}\), the factor \(1/(d\phi(d))\) and the harmonic \(1/\phi(r')\) sum are power-small after taking out \(1/\phi(s k)\). This is the exact sign cancellation for \(\mu(r)\); no positive \(\sum |\mu(r)|\) reference is dropped. Summing \(\Lambda(k)/\phi(k)\), \(1/\phi(s)\), and the source weights costs only fixed log powers, giving the same \(O_D(xL^{-D})\) reserve for the principal. This proves (3).

## 4. What survives in the full positive triprime chamber

For any fixed compact reflected triprime box \(\mathcal B\) encompassing this m-profile, all individual factors are \(<.41\) and their pairs \(>.59\), so \(C=+\log m\) throughout. One can use the full reverse Vaughan opening there before making the high-block selection: the two short \(q\)-pieces have moduli \(s r\) or \(s r k\) with \(r\le U_q,k\le V_q\), hence exponent at most \(.22\). The source is an SW genuine prime times the independent convolution of the other two primes; apply generalized BV as in [FullScaleConvolutionBV.md](FullScaleConvolutionBV.md) with both slots polynomial. The first short harmonic mean is
\[
 {\mathcal R}_{\mathcal B}
 =\sum_{\substack{s\ {\rm as\ above},\ m\in\mathcal B\\(s m,N)=1,\ (s,m)=1}}
  \frac{\mathfrak S(N m)}{s-1}\,
  \frac{W_s((N-m)/s)\log m}{\log((N-m)/s)} ,
\]
up to arbitrary log error. To see its sign and exact normalizing factor, \(r\le U_q<s\), so take out \(1/(s-1)\) and apply the \(\mu/\phi\) constant moment and the weighted logarithmic moment with mask \(N m\), since \(\log(q/r)=\log(q/U_q)+\log(U_q/r)\). In the second short term these are just constant moments after fixing \(k\), treating \(r,k\) overlap by the same exact local ratio as above. Thus that piece is negligible. Removing proper prime powers when replacing \(\Lambda(q)/\log q\) by the prime indicator costs \(x^{.6+o(1)}\) after all true \(s\) labels. The full true \(q\)-prime mass on \(\mathcal B\) equals this **positive** reference plus the entire opened reverse remainder. Equation (3) removes only the specified high coupled tube from that remainder. In particular it is not cancellation of the full true \(q\)-prime mass, nor cancellation of the ungroupable near-equal \(m\)-triprime profiles.

[Pham's October 2026 preprint](https://www.preprints.org/manuscript/202610.3061), §8 and Appendices B–E, also studies fixed-target reflected weights and their signed boundary; its general prime–prime term stays open. The calculation above is specific to this three-prime source and this opened (q)-block.

Related [Chan's Theorem (1+1.75), v1.0](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf), Proposition 4.1, is a nonnegative bounded-rank prime-product upper consequence under its admitted fixed geometric restrictions, not an estimate for this signed reverse convolution. Even granting application of its \(K=6.7617368\) to the true comfortably unbalanced \(s q\) source over the whole original band, its cap on the positive prime-reflected term would be \(K/2=3.3808684\) times our matched reference. With \(J=\log(7/5)-.16+.0192\) this allows about \((K/2-1)J\,M_N=.46587 M_N\), not the needed \(.010 M_N\). The published signed bounds here and the two preprint inputs do not close that gap.
