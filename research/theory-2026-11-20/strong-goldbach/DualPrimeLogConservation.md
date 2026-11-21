# Whole-ledger projection onto two genuinely large prime tags

The one-leg log conservation left a required **negative** large-\(m\)-tag sum of about \(-.08999 M_N\). There is a broad, signed, fixed-target term on this very operator that pays its entire new calibration: the actual \(q\) tags below a full product-BV threshold. After this second conservation step the original sufficient \(.010 M_N\) cap is needed **only** on a product of two high-tag weights. No upper on that final doubly high signed operator is claimed.

## 1. Physical statement

Keep \(N=2x,L=\log x,M_N=\mathfrak S(N)x/(2L)\), actual prime \(s\in(x^{.10},x^{.14})\), \(n=sq\in(x/2,x]\), \(m=N-n\), units \((n,N)=1\) and \(W_s(q)=(1-t)(1-2t)^2\) at \(t=\log s/\log n\). Put \(J=\log(7/5)-.1408\). Fix smooth compact \(f,h\), with \(f(t)=1-t\) and \(h(t)=1\) near \(0\), and positive-side supports \(.001\) and \(c\le .400\) respectively. Set
\[
 H_g(u)=\sum_{d\mid u}\mu(d)g(\log d/\log u),\qquad
 X_h(s,q)=W_s(q)(\log m)H_h(q)H_f(m).
\]
Keep exactly the same centered \(E_N\) as in [ReflectedPrimeLogConservation](ReflectedPrimeLogConservation.md).

Choose \(a\) with
\[
 .90c\le a,\qquad .140+.860c+a<1/2,                                    \tag{1}
\]
with a strict fixed margin in the second inequality. Write \(B=.489\), and put
\[
 U_0(q)=\sum_{\substack{p\mid q,\ p\ {\rm prime}\\p\le x^a}}\frac{\log p}{\log q},
 \quad U_1(q)=\sum_{\substack{p\mid q,\ p\ {\rm prime}\\p>x^a}}\frac{\log p}{\log q},
 \quad V_1(m)=\sum_{\substack{r\mid m,\ r\ {\rm prime}\\r>x^B}}\frac{\log r}{\log m}.
\]
Each logarithmic tag is counted once per distinct actual prime. Then uniformly for every even target,
\[
 \sum_{s,q;\,q,m\ {\rm composite}} X_h(s,q) U_0(q)V_1(m)
       =-(1-B)J M_N+o(M_N),                                           \tag{2}
\]
and
\[
 E_N=\sum_{s,q;\,q,m\ {\rm composite}} X_h(s,q)U_1(q)V_1(m)+o(M_N).
                                                                         \tag{3}
\]
Examples are \(c=.200,a=.180\), with largest actual quotient modulus exponent .492, and \(c=.001,a=.357\), with exponent .49786. These are different kernel choices, not additive credits. For both, (3) has the original centered \(.010 M_N\) required cap. Since \(p>x^a\ge q^c\) and \(r>x^B>m^{.001}\) eventually, neither high tag enters its own short score. Thus the remaining exact operator really has actual independent prime labels \(p,r\) in
\[
 s p u + r v=N,\qquad u=q/p\ge2,\ v=m/r\ge2 ,
\]
with those same normalized tag weights, and the signed divisor scores on \(u,v\) (the original denominators \(\log q,\log m\) remain). The residual prime labels need not be unique.

## 2. Full-scale BV on the actual marked reflected sequence

Open a low \(p\mid q\) and a high \(r\mid m\) in the expression on the left of (2). All such \(p\)'s are proper, since (1) implies \(a<.360\) and \(q\gg x^{.86}\); no \(q\)-prime atom is included. Put \(m=r v\), explicitly \(v\ge2\) since \(m\) is composite. If \(r\) repeats in \(v\), the tag is still counted just once and every active reflected divisor is smaller than \(r\). Hence the reflected score is \(H_f(v;m)=\sum_{e\mid v}\mu(e)f(\log e/\log m)\) exactly. In \(H_h(q)\) split the \(p\)-bit, including if \(p^j\mid q\), and open \(p d\mid q\), \((p,d)=1\), with weight
\[
 g_p(\log d/\log q),\qquad
 g_p(t)=h(t)-h(t+\log p/\log q).
\]
Rows with \(s\mid q\) cost \(x^{.90+o(1)}\) absolutely, by \(\sum_s(x/s^2+1)\) and divisor bounds. Delete them first, so \(p\ne s\) and \(s\nmid d\); they can be restored when counting geometric or BV rows under those fixed divisor masks with the same power-small error. All primes have the literal target-unit masks. In particular the actual modulus \(F_0=s p d\) is coprime to \(N\); it has size \(\le x^{.140+.860c+a}\), since \(d\le(x/s)^c\). Its number of opened \((s,p)\) labels is at most \(\omega(F_0)^2=O(L^2)\), an admissible log loss. The residue for the actual \(m=r v\) sequence is \(N\bmod F_0\).

Apply the [full-scale product BV theorem](FullScaleConvolutionBV.md) to the \(r\times v\) source at the scale \(x\), with \(r\) a true prime SW factor carrying \(\log r\), and \(v\) an independent divisor-bounded factor. For \(v\ge x^\eta\), \(\eta>0\) fixed small, both lengths are polynomial. For \(2\le v<x^\eta\) use ordinary prime BV for \(r\) at scale \(x/v\) and residue \(N\bar v\bmod F_0\), reduced whenever \((v,F_0)=1\); incompatible \(v\)'s give no rows. Choose \(\eta\) so that \(1/2-\eta/2\) exceeds the strict exponent in (1), and sum these errors with \(\sum_{v\le x^\eta}\tau(v)/v\ll L^2\). On both sides \((v,N)=1\) is part of the physical units, and any exceptional \(r\mid N\) is removed as an independent prime mask on the SW factor. A prime \(r>x^B\) cannot divide \(F_0\).

Here is the weight separation for this application. On log-power fine product meshes freeze \(m\) in \(f(\log e/\log m)\), **without opening \(e\)** in the BV sum: it makes \(H_f(v;m)\) one divisor-bounded \(v\) coefficient. The error from freezing is paid by the global fixed divisor moments on the physical and centered model sums, while \(r v\) inside the box still has its actual progressing residue. The remaining \(s,p,d\)-dependent smooth \(m\) tests (from \(W_s(q)\), \(g_p\), and \(\log q\)) have uniformly log-bounded variation and may be frozen on that mesh or treated as prefixes. Ranges \(r>x^B,v\ge2\), units in either factor, the product interval and all fixed dyad divisions preserve the actual prime SW condition as in the full-scale note. Each modulus has only the stated polylogarithmic number of physical labelings; arbitrary log reserve in BV covers all meshes and the weights. No factor of \(x^{.001}\) is charged to BV. In the principal, the actual \(r\) weighted by \(\log r\) is integrated using ordinary PNT at its polynomial scale, for fixed \(v\): all other functions of \(m=rv\) are bounded-variation tests after expansion, with divisor-bound coefficients, so the harmonic \(v\)-sum costs a log power. The omitted primes \(r\mid N\), all \(\ge x^B\), cost at most \(x^{1-B+o(1)}\) there after those harmonic modulus sums. This proves the principal with arbitrary log reserve, not just an equality after averaging over targets.

Now use \(dm/v=dr\) and \(q=(N-m)/s\). Write \(F=N s p\) and \(Y=m/x^B\). The literal principal is
\[
 \sum_{\substack{s,p\ {\rm prime}\\(sp,N)=1,\ s\ne p,\ p\le x^a}}
 \frac{\log p}{\phi(sp)}
  \int_x^{3x/2}\frac{W_s(q)}{\log q}
   \sum_{\substack{(d,F)=1}}\frac{\mu(d)}{\phi(d)}
       g_p(\log d/\log q)
       \sum_{\substack{2\le v<Y\\(v,Fd)=1}}
             \frac{H_f(v;m)}v\, dm.                                  \tag{4}
\]
The factor \(1/\log q\) is from the low \(p\) logarithmic weight; the outer \(\log m\) has canceled with the high \(r\) weight. In particular (4) must **not** use an absolute \(v\)-sum after evaluating the \(d\) factor: that would lose the required reserve and misprice the term.

## 3. Finite harmonic evaluation with the missing \(v=1\) atom

For any polynomial mask \(D\), let \(C_D=D/\phi(D)\) and \(\mathcal L_D=\sum_{\ell\mid D,\ \ell\ {\rm prime}}\log\ell/(\ell-1)\). Uniformly \(Y=m/x^B\asymp x^{1-B}\) and \(T=\log m\), the inner \(v\)-sum in (4) is
\[
 \sum_{\substack{2\le v<Y\\(v,D)=1}}\frac{H_f(v;m)}v
  =\frac{\log Y-\gamma-\mathcal L_D}{T}+O_A(L^{-A}),                  \tag{5}
\]
where \(\gamma\) is Euler's constant. To prove this, first include \(v=1\) and open \(v=e k\). For \(e\) on the support, \(Y/e\) is polynomially long. Ordinary coprime harmonic counting, by inclusion-exclusion in \(D\) and \(H_j=\log j+\gamma+O(1/j)\), gives
\[
 \sum_{k<Y/e,\ (k,D)=1}\frac1k
    =C_D^{-1}(\log(Y/e)+\gamma+\mathcal L_D)+O_A(L^{-A}).
\]
The uniform tail beyond \(Y/e\), if needed in the divisor expansion of the mask, is power-small with fixed Rankin exponent \(1/4\), since \(\prod_{\ell\mid D}(1+\ell^{-3/4})=x^{o(1)}\). Use the finite coprime signed moments of \(\mu(e)/e\), valid with arbitrary log reserve on any fixed polynomial length: convolution with the smooth-at-\(D\) Euler factor of \(1/\zeta(1+z)\) proves the uniform cumulative tail, and partial summation then allows each fixed log moment. Explicitly the Taylor expansion is
\[
 \sum_{(e,D)=1}\frac{\mu(e)}{e^{1+z}}
  =C_D[z-(\gamma+\mathcal L_D)z^2+O_D(z^3)].
\]
The affine neighborhood of \(f\) gives, with arbitrary log errors,
\[
 \sum_{(e,D)=1}\frac{\mu(e)}e f(\log e/T)=C_D/T,\qquad
 \sum_{(e,D)=1}\frac{\mu(e)\log e}e f(\log e/T)
       =-C_D+2C_D(\gamma+\mathcal L_D)/T.
\]
For rigor, replace the tests by their affine forms for \(e\le x^\epsilon\) where the equality is exact, and use the uniform signed cumulative tails for larger arguments with partial summation. The coefficient \(C_D\) in each formula cancels \(C_D^{-1}\). Finally remove \(v=1\), whose score is exactly \(f(0)=1\); this yields (5). Including \(v=1\) incorrectly would change the final constant by \(J\).

Apply (5) in (4) **before** the \(d\)-sum. The constant part of \(\mathcal L_{F d}\) is \(\mathcal L_F=O(\log L)\); the rest is \(\mathcal L_d\) because \((d,F)=1\). Use the finite signed \(\mu/\phi\) harmonic of [ReflectedPrimeLogConservation](ReflectedPrimeLogConservation.md):
\[
 \sum_{(d,F)=1}\frac{\mu(d)}{\phi(d)}g_p(\log d/\log q)
 =\frac{\mathfrak S(F)}{\log q}\,h'(\log p/\log q)
       +O_{h}\!\left(\mathfrak S(F)\frac{1+\log L}{L^2}\right);
\]
here \(-g_p'(0)=h'(\log p/\log q)\) because \(h\) is flat near zero. For the term containing \(\mathcal L_d\), open \(\ell\mid d\) and use the same uniform harmonic for the shifted \(g_p\) and mask \(F\ell\). The opened factor has absolute size \(\log\ell/(\ell-1)^2\), whose prime sum converges, so the \(\mathcal L_d\)-weighted \(d\)-sum is \(O_h(\mathfrak S(F)/L)\), not a crude absolute harmonic loss. Its factor \(1/T\) in (5) gives a strict additional \(1/L\). All other errors (including the arbitrary-log one in (5)) now sum to \(o(M_N)\) under the external harmonic label sums. The factor \(\log Y/T\) is \((1-B)+O(1/L)\).

In the leading \(p\) sum, \(h'(\log p/\log q)\ne0\) only at polynomially large \(p\), since \(h\) is exactly flat close to \(0\). Thus omissions at \(p\mid Ns\) and the ratio \(\mathfrak S(Nsp)/\mathfrak S(Ns)\) cost power-small errors in that leading coefficient. The prime logarithmic harmonic sum, with its smooth bounded-variation test, gives
\[
 \sum_{p\le x^a}\frac{\log p}{\phi(p)}h'(\log p/\log q)
  =\log q\int_0^{aL/\log q} h'(t)\,dt+o(L)
  =-\log q+o(L),
\]
uniformly on the physical interval. In the last step \(aL/\log q\ge c\) by (1) and \(\log q\le.90L\), \(h(0)=1,h(c)=0\). This is the **negative** source in (2). Finally \(\mathfrak S(Ns)=\mathfrak S(N)(1+O(1/s))\) for the allowed genuine \(s\), and
\[
 \int_x^{3x/2}\sum_{\substack{s\ {\rm prime}\\ x^{.10}<s<x^{.14},\ (s,N)=1}}
                  \frac{W_s(q)}{\phi(s)\log q}\,dm
     =(J+o(1))\frac{x}{2L},
\]
by the prime harmonic sum and \(\log q=(1-\log_x s)L+O(1)\) on the entire physical interval. This proves (2) at each target. Repeated \(r\) or \(p\) and the precise missing \(v=1\) endpoint were not identified with a surrogate prime.

## 4. The remaining true large-large problem

The complete low-reflected tag term is \(+(1-B)J M_N+o(M_N)\) by reflected conservation, and (2) pays exactly this known term on the remaining actual large reflected band. The independent bilateral small-factor and squareful bounds apply to the present fixed kernels, so \(1-U_0-U_1\) is supported on a set with absolute \(o(M_N)\) total. (First use any fixed small rough threshold, then take it down to zero.) Hence subtracting (2) from that remaining operator gives (3). This neither reuses the earlier wide-kernel reserve nor assumes a cancellation estimate on an arbitrary pair of high tags.

In (3) the support involves two real labelled primes in the same equation. Its difficult part is not a common null for a freely varying divisor, but a signed sum on those large labels with their genuine cofactors and the moving target; candidate progression theorems must admit those factor sizes and moduli. The portion of (3) that is already covered by [BalancedLargeTagTaper](BalancedLargeTagTaper.md) can still be excised **only for its own short-kernel variant**. No result here establishes the required bound on the doubly high remainder or proves Goldbach.
