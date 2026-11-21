# An exact signed cancellation for large actual tags in the balanced semiprime band

We prove a uniform signed removal in the **whole original Goldbach ledger**, after an explicitly permitted change to shorter smooth kernels. A nonnegative taper removes at least \(12.4\%\) of every actual balanced semiprime-by-semiprime adverse row specified below; a narrower unweighted mask is removed completely. Neither removal is based on a positive-only envelope or on averaging the signed statistic over targets. The uncovered residual, and the different smooth-kernel reserve from earlier notes, are not controlled here.

## 1. Physical rows and the precise removal

Keep the even target \(N=2x\), \(L=\log x\), \(M_N=\mathfrak S(N)x/(2L)\), and the actual rows
\[
 s\ {\rm prime},\quad x^{.10}<s<x^{.14},\quad n=sq\in(x/2,x],\quad
 m=N-n,\quad (n,N)=1,\quad W_s(q)=W(\log s/\log n),
 \quad W(t)=(1-t)(1-2t)^2 .
\]
Take fixed \(f,h\in C_c^\infty(\mathbb R)\) of support \([-.001,.001]\), with \(f(t)=1-t\) exactly near zero, and \(h(t)=1\) exactly near zero. Write \(H_g(u)=\sum_{d\mid u}\mu(d)g(\log d/\log u)\) for \(u>1\), and \(X_h(s,q)=W_s(q)(\log m)H_h(q)H_f(m)\). The identity of [BilateralSmoothRoughReduction](BilateralSmoothRoughReduction.md) remains valid verbatim:
\[
 E_N=\sum_{\substack{s,q\\q,m\ {\rm composite}}} X_h(s,q)+O_A(xL^{-A}).   \tag{1}
\]
In fact the proof of the original smooth replacement uses only the exact affine neighborhood for \(f\), the strict upper bound \(f\)'s support \(<1/2\) (the earlier \(.310\) is not a lower bound), and log-bounded variation. Its finite coprime \(\mu/d\) and \(\mu/\phi(d)\) means keep exactly the same normalization for this shorter \(f\). All short or switched moduli and floors in that proof still fit. The second whole null for \(h\) has \(sd\le x^{.141}\) here, so its ordinary BV step is also valid. Prime atoms are unchanged exactly and the same proper-prime-power estimates apply. This uses no numerical reserve from the \(.310\) kernel.

Let \(S=2^j\) be the unique dyadic block with \(S<s\le2S\). Define the true prime tag sets per block
\[
  \mathcal P_S=\{p\ {\rm prime}: x^{.340}<p<x^{.010}\sqrt{x/(2S)}\},
 \qquad
  \mathcal R=\{r\ {\rm prime}:x^{.300}<r<x^{.506}\}.
\]
Set
\[
 U_S(q)=\sum_{\substack{p\mid q\\p\in\mathcal P_S}}\frac{\log p}{\log q},
 \qquad V(m)=\sum_{\substack{r\mid m\\r\in\mathcal R}}\frac{\log r}{\log m}.
\]
Both lie in \([0,1]\) exactly, including when a divided leg is not squarefree. We prove
\[
 \sum_{s,q} X_h(s,q) U_S(q)V(m)=O_A(xL^{-A}).                            \tag{2}
\]
Only composite legs can occur in (2), since both tags are proper factors in the physical intervals. The weighted sum may include prime powers; they are already negligible in (1), and no prime-power exclusion is needed for (2).

There is also an **unweighted** complete near-balance mask:
\[
 \mathcal P_S^{\rm u}=\{p\in\mathcal P_S:p>x^{.001}\sqrt{x/S}\},
 \qquad
 \mathcal R^{\rm u}=\{r\in\mathcal R:r>x^{.501}\}.
\]
Replace \(U_S V\) in (2) by \(1_{\{\exists p\in\mathcal P_S^{\rm u}:p\mid q\}}1_{\{\exists r\in\mathcal R^{\rm u}:r\mid m\}}\). For large \(x\), any tag in these restricted bands is larger than the square root of its own leg, so it is unique and occurs to exponent one, and the signed sum still satisfies (2).

In particular, subtracting (2) from (1) gives the exact same criterion with nonnegative row taper \(1-U_S(q)V(m)\). On each **actual** row where \(q\) is a semiprime with \(P^-(q)\ge q^{.4}\) and \(m\) a semiprime with \(P^-(m)\ge m^{.31}\), both short scores equal 1. The smaller prime of \(q\) lies in \(\mathcal P_S\): \(q\ge x/(2s)\) gives \(q^{.4}>x^{.340}\) eventually, and the upper endpoint is above \(\sqrt{x/S}\) eventually. The smaller prime of \(m\) is in \(\mathcal R\) by the central range and strict margins at exponents \(.300,.506\). Thus \(U_S\ge.4\), \(V\ge.31\) and at least \(.124\) of the original positive weight \(W_s(q)\log m\) is removed on **every** such row. The same positive semiprime weights held on the interior of this profile for the earlier broad reflected kernel. The full unweighted mask removes its own positive rows completely. What replaces this part of the full sum is exactly zero up to arbitrary log reserve, because the other actual factorization ranks in the removed term are **signed**, not dropped.

## 2. Opening the true factors, including the unit condition

In either version, open actual \(p\mid q,r\mid m\) and the short divisors \(d\mid q,e\mid m\) in the two scores. Divisor support implies \(d,e\le x^{.001+o(1)}\); thus no divisor argument contains a tag or \(s\). The physical unit condition forces \((s p r d e,N)=1\), and \((p,r)=1\) and \((d,e)=1\). No other coprimality of short divisors with the three macroscopic primes is needed, since their sizes already ensure it. In particular if the tag bands intersect, the coincident \(p=r\) term is truly empty. We may use \(q=p d u\) and \(m=r e v\), **even if** the quotient still contains one of its own tags: \(d,e\) cannot contain these primes. After these restrictions \((n,N)=1\) is exactly \((u,N)=1\).

Expand the latter as \(\sum_{g\mid(u,N)}\mu(g)\). Terms with \(g>x^{.0001}\) contribute \(O(x^{1-.0001+o(1)})\) to the full signed weighted sum. Indeed \(g\mid n\), so there are \(O(x/g+1)\) actual \(n\)'s per \(g\mid N\); all original choices \(s,p,r,d,e\), weighted or not, and score factors are bounded at given \(n\) by a fixed power of \(\tau(n)\tau(N-n)L\). The target divisor count is \(x^{o(1)}\). This truncation does not discard rows just because the two original legs share a prime; it estimates the explicitly opened large-\(g\) part.

Write \(u=g w\), \(P=r e\). The actual residue of \(w\) is
\[
 w\equiv N\overline{s p d g}\pmod P.                                     \tag{3}
\]
It is reduced after the stated restrictions. In particular \((s,P)=1\) by sizes, \((g,P)=1\) because \(P\) is prime to \(N\), and \((d,P)=1\) by \((d,e)=1\) and sizes. We may keep \((p,P)=1\) explicitly throughout. Also \(P\) is squarefree whenever \(\mu(e)\ne0\), with the large prime \(r\nmid e\).

Use a smooth central weight in \(n/x\), identical to the sharp interval off two bands of length \(O_A(xL^{-K})\) and with \(j\)-th derivatives \(O_j(L^{Kj})\). Replacing the endpoints in either direction costs \(O_A(xL^{-A})\) by taking \(K\) large. Indeed at each actual \(n\) the absolute weight is bounded by \(L^C\tau(n)^C\tau(m)^C\) for a fixed \(C\), including the opened labels and optional divisors \(g\mid n\). On either endpoint interval apply Cauchy and [Shiu's short-interval bound](https://doi.org/10.1515/CRLL.1980.313.161) to the two fixed divisor powers individually on the \(n\) interval and its reflected \(m\) interval. Their lengths are \(\gg x^{.99}\), so this gives the claimed log reserve. All subsequent smooth weights are supported in a fixed compact central range where \(n,m\asymp x\).

## 3. A power saving on the complete nonzero frequency range

Split \(p,r,d,e\) into dyadic boxes, allowing the unit or fractional end intervals. The actual \(p\)-range is a fixed interval **within each \(S\)**, including in the unique-tag version; no cut depends on the varying prime \(s\) inside that block. Write the sizes as \(S,A,B,D,E\) respectively for \(s,p,r,d,e\), with
\[
 \sigma=\log_x S,\ \alpha=\log_x A,\ \beta=\log_x B,\ 
 \delta=\log_x D,\ \epsilon=\log_x E,\ \gamma=\log_x g,
\]
so \(\sigma\le.14+o(1)\), \(\alpha\le(1-\sigma)/2+.010+o(1)\), \(\beta\le.506+o(1)\), \(\delta,\epsilon\le.001+o(1)\), \(\gamma\le.0001\). The lower tag bounds are \(\alpha\ge.340+o(1)\), \(\beta\ge.300+o(1)\).

For fixed \(d,e,g,r\), apply Poisson to (3), with free scale \(V_0=x/(s p d g)\). Separating the smooth weights costs only a log power per box. Here are explicit details of this separation. On the \(S\) block the \(n/x\) test has smooth dependence on \(\log(s/S)\) in a compact interval, as do \(W_s\), \(\log m\), the two functions of \(d,e\) with moving denominators, and, for logarithmic marks, \(1/\log q\) and \(1/\log m\). Extend with a fixed smooth cutoff in this variable and Fourier-expand. The \(L^1\) norms of the coefficients of each needed derivative of the \(n/x\) test are \(O(L^C)\) by integration by parts twice in the compact variable. The remaining factors \(\log p,\log r\) are separated from the argument. The resulting Poisson expressions have nonzero frequency \(k\) and amplitude
\[
 \frac{V_0}{P}\,\widehat \Phi(kV_0/P)
\]
where \(\Phi\) no longer depends on \(s,p\) except through separated factors. On a signed dyad in \(k\), Fourier-expand the amplitude as a smooth function of \(\log(|k|V_0/P)\), after a fixed cutoff on a compact interval around its dyadic center. This separates \(s,p,k\) because \(V_0=x/(s p d g)\). The \(L^1\) norm is still \(O(L^C)\) times the size of \(V_0/P\): fixed logarithmic derivatives of \(\widehat\Phi\) are uniformly bounded by fixed derivatives of the compact \(\Phi\), also when \(|k|V_0/P>1\), by integration by parts. The smooth dependence on \(s\) is therefore not replaced by an arbitrary coefficient depending on \(p\). All powers of \(L\) in the separation may depend on the desired endpoint reserve \(K\).

Truncate at \(|k|\le T\) with \(T\asymp (S A D g B E/x)x^{.0002}\), independent of \(s,p\) within the box. The omitted rapid Fourier tail is power-small by sufficiently many integrations; each derivative norm costs only log powers. If \(T<1\) there is no term. Otherwise put \(t_*=\alpha+\beta+\sigma+\delta+\epsilon+\gamma-1+.0002\) (allowing \(o(1)\) for constants). The dyadic bounds give \(T<\min(s)\) by a power reserve, since \(\alpha+\beta+\delta+\epsilon+\gamma+.0002\le.9683+o(1)\); also \(ST\ll r x^{-c_1}\) for a fixed positive \(c_1\), since \(2\sigma+\alpha+\delta+\epsilon+\gamma+.0002<.75\) up to \(o(1)\). For two pairs \((s,k),(s',k')\), equality
\[
 k s'\equiv k's\pmod r
\]
thus implies literal equality of the integers. Since \(s,s'\) are prime, \(k,k'\ne0\), and both frequencies are shorter than either matching prime, this forces \(s=s'\) and \(k=k'\), when all labels are in the given block. This is where the short source prime is used. Using arbitrary \(s\)-coefficients supported on integer composites instead would not justify this assertion.

After separation the weighted sum over \(p,s,k\) is bounded by estimating
\[
 \sum_{p\in I,\ (p,P)=1}\eta_p
       \sum_{s,k}\lambda_s\omega_k
          e^{2\pi i kN\overline{s p d g}/P} ,
\]
where \(\eta_p\) is supported on actual primes \(p\) in its interval \(I\) of length \(O(A)\), and the coefficients are 1-bounded after log normalizations. Keep the actual \(s\)-prime condition. Cauchy drops the prime restriction in the *second moment on that interval*, not on all classes of the modulus. The diagonal costs \(A ST\) in this second moment. Every off-diagonal phase has difference
\(C=N\overline{dg}\,(k\bar s-k'\bar s')\) whose residue modulo \(r\) is nonzero. Thus \((C,P)\le e\). Completion of the inverse exponential over the interval, and the [Weil bound](https://doi.org/10.1073/pnas.34.5.204) on each prime factor of the squarefree modulus, give \(x^{o(1)}\sqrt{P(C,P)}\ll x^{o(1)}\sqrt B\,E\) on its incomplete period. Any whole periods cost at most \(O((A/P+1)(C,P))\), via the Ramanujan sum. This adds at most \(O(A/B+E)\), which is covered by \(\sqrt B\,E\) in every nonzero-frequency box: \(T\ge1\) forces \(\beta\ge .4177+o(1)\) from \(\alpha+\sigma\le.580+o(1)\) and the small-factor exponents. In particular \(A/B\ll B^{1/2}\) with reserve. The completed Weil factors depend on the *square root* of \((C,P)\); it was not assumed that \(C\) is a unit at \(e\).

The resulting bound on the trilinear sum is
\[
 x^{o(1)}\Big[A\sqrt{ST}+\sqrt A\,ST\,B^{1/4}E^{1/2}\Big].              \tag{4}
\]
Multiplying by the Poisson size \(x/(S A D g B E)\) and summing the actual \(r,d,e\) at cost at most \(BDE\), the diagonal and off-diagonal exponents, respectively, are
\[
 1+\tfrac12(\alpha+\beta+\delta+\epsilon-1-\gamma+.0002),\qquad
 \tfrac12\alpha+\sigma+\tfrac54\beta+\delta+\tfrac32\epsilon+.0002 .
\]
They are bounded by \(.9841+o(1)\) and \(.9952+o(1)\); for the second use \(\alpha/2+\sigma\le .255+.75(.14)=.360\). The number of dyads and divisors \(g\mid N\) and all separations cost \(x^{o(1)}\). This proves power saving on **all** nonzero frequencies in the stated sector, not merely those near zero.

## 4. The zero mode, and physical support

The zero mode of (3) is the literal geometric density in \(q\), namely \(1/(p r d e g)\) times the smooth physical integral. Restoring all \(g\mid N\) costs \(O(x^{1-.0001+o(1)})\) also in this density, by its absolute harmonic bound and the \(g^{-1}\) tail. The exact unit factor is then \(\phi(N)/N\). In the short-divisor pair, \((d,e)=1\) and \((de,Nspr)=1\) are the same masks as in [BilateralTrueTagCovariance](BilateralTrueTagCovariance.md). Here \(p,r\) are both beyond the supports, so the kernels of the opened divisors are simply \(h,f\), without any shifted prime-bit contribution. The \(d,e\) principal therefore contains the finite joint harmonic sum
\[
 \sum_{\substack{(d,e)=1\\ (de,Nspr)=1}}
 \frac{\mu(d)\mu(e)}{de}
   h(\log d/\log q)\, f(\log e/\log m).
\]
This has arbitrary log reserve since **\(h\) is exactly flat near zero**, not just \(h'(0)=0\). For clarity, use the absolutely convergent rankin-margin bivariate Euler convolution in the true-tag note. For shifts \(D,E\) in that convolution with \(D\le x^{c_2}\) for a sufficiently small fixed \(c_2>0\), evaluate the \(d\) leg by partial summation against the cumulative coprime \(\sum_{n\le e^t,(n,Nspr)=1}\mu(n)/n\). The first derivative of \(h((t+\log D)/\log q)\) is supported on \(t\ge c_2L\), uniformly in the final \(q\) interval. The cumulative coprime sum there is \(O_A(L^{-A})\): convolve the unrestricted cumulative sum with \(j^{-1}1_{j\mid(Nspr)^\infty}\), split \(j\) at \(e^{t/2}\), use ordinary Möbius PNT with log reserve on the short part and a Rankin bound on the remaining \(j\)'s. The latter loses \(e^{o(L)}\), by the polynomial modulus \(Nspr\); its exponential gain is retained. For \(D>x^{c_2}\) the Euler convolution's fixed Rankin margin pays a power saving. The \(f\) leg needs only its bounded harmonic absolute sum and the convolution. This proves the zero-mode cancellation uniformly at the true moving endpoints. The extra factors in either tag test have uniform log-bounded size/variation, and summing the harmonic prime labels retains all desired log reserve.

Together with the smoothing and the nonzero bounds, this proves (2) in both forms. The unweighted unique mask contains a positive-width family of actual adverse semiprime-by-semiprime profiles. For example take \(s\) near exponent \(.1225\), the larger \(q\)-prime with exponent near \(.44425\), and the larger \(m\)-prime near \(.503\). With sufficiently small fixed independent exponent neighborhoods, the smaller primes of \(q,m\) are near \(.43325,.497\), all bands disjoint, and the stated unique cuts hold even allowing the dyadic endpoint constants. These geometry constraints are actually occupied in dyadic aggregate: for \(n\in(.70Y,.71Y),m\in(1.30Y,1.31Y)\), independently choose the true \(s,p,r\) in their fixed exponent bands and use PNT on the last factors in the respective product intervals. The total is \(\gg Y^2/\log^2Y\) genuine pairs, with \((n,m)=1\) by the disjoint bands, even targets \(N=n+m\), and the positive weights \(\log m\) on the appropriate scale. This occupancy observation is **not** an assumption of fixed-target lower occupancy in the proof. Equation (2) is itself a fixed-target assertion; wherever such adverse rows occur they are signed-compensated within the selected contribution.

The remaining full sum has the row-dependent taper \(1-U_S V\), or the complement of the unique mask, and it still lacks a sufficient signed upper cap. No older wide-kernel debit is spent here. The theorem gives an actual partial cancellation on a wide same-equation factor window and an exact complete cancellation on one near-balanced mask, not a proof of Goldbach.

The broad distribution theorems of [Wright](https://arxiv.org/abs/2608.27732) and [Jain](https://arxiv.org/abs/2611.21136) concern different convolution hypotheses. The estimate here uses only Poisson, the prime-source injection of \((s,k)\) into the residue phase, and interval completion after Cauchy; it does not import a theorem for primes in arbitrary moduli or an independence assumption for the two tags.
