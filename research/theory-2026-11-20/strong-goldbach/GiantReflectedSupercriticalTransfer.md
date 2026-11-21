# A whole giant-reflected sector beyond the prime-tag diagonal

In the actual two-high signed ledger there is a broad \(p<r\), \(pr>x\) sector where no additional prime marker is needed. Put the **short cofactor of the genuine reflected prime** in Lichtman's Siegel–Walfisz slot, and the actual \(s,p\) in separate modulus slots. The complete original sector is \(o(M_N)\); only its subpower-rough branch has arbitrary logarithmic reserve.

## 1. Exact scope

Keep the setting of [SpectralSubcriticalPrimeProduct](SpectralSubcriticalPrimeProduct.md): \(N=2x,L=\log x\), actual prime \(s\) with \(x^{.10}<s<x^{.14}\), \(n=sq\in(x/2,x]\), \(m=N-n\), \((n,N)=1\), and the original short \(C_c^\infty\) kernels \(h,f\), with positive-side supports \(.001\), \(h(t)=1,\ f(t)=1-t\) near zero. The signed summand is exactly
\[
  X_h(s,q)\frac{\log p}{\log q}\frac{\log r}{\log m},\qquad
  X_h(s,q)=W_s(q)(\log m)H_h(q)H_f(m),
\]
where \(p\mid q,r\mid m\) are true primes above the dual projection cutoffs \(.359,.499\). Work on any fixed closed independent exponent box strictly in
\[
 .10<\sigma<.14,\qquad \alpha>.359,\qquad \beta<.998,\qquad
                      2(1-\beta)+\sigma+2\alpha<1,                       \tag{1}
\]
where \((\sigma,\alpha,\beta)=(\log_x s,\log_x p,\log_x r)\). The last condition forces
\(\beta>.5+\alpha+\sigma/2>.909\), so \(p<r\), \(pr>x^{1.268}\), and both original legs are composite with polynomially long cofactors. Then the complete genuine signed contribution of this box is
\[
 O_{h,f,\text{box}}\!\left(\frac{M_N}{(\log L)^3}+x^{.98}\right)
                     =o(M_N),\qquad M_N=\frac{\mathfrak S(N)x}{2L}.        \tag{2}
\]
For instance \(.101\le\sigma\le.109,\ .415\le\alpha\le.425,\ .985\le\beta\le.992\) fits with \(s p>x^{.516}\) before adjoining any short modulus factor. This is not the elementary original dual projection with \(s p d<x^{1/2}\).

More precisely let \(z_*=x^{2/(\log L)^3}\). The portion with \(P^-(m)>z_*\) is \(O_C(xL^{-C})\) for every fixed \(C\). After restoring all omitted physical rows the proven absolute error is as in (2), not arbitrary log reserve on the whole box.

## 2. Error on the omitted physical rows

In the old absolute [bilateral small-factor estimate](BilateralSmoothRoughReduction.md), Section 2, take \(\kappa=2/(\log L)^3\), so \(x^\kappa=z_*\). Its \(m\)-leg bound improves to \(O_{h,f}(\kappa M_N+x^{.98})\) here: with the present \(C_c^\infty\) reflected kernel the last Fourier integral contains
\[
   \int_{\mathbb R}(1+|\eta|)^2|\eta|\,|\widehat f(\eta)|\,d\eta<\infty,
\]
so the linear bound on the extracted local factor suffices directly (the former cosine kernel needed \(\kappa\log(2/\kappa)\)). This upper bound is uniform in the small parameter and uses absolute **actual** \(X_h\). The product of the summed normalized distinct prime logs over any \(p,r\) box is at most 1, since each leg has \(\sum_{\ell\mid u}\log\ell\le\log u\). Hence the deleted physical portion itself has the bound in (2), without assigning it a sign or assuming roughness of its other leg.

On the retained rows write \(m=r e k\), opening the \(f\)-score on \(e\mid m/r\). Since \(r>x^{.909}\) and \(e\le (1.5x)^{.001}<r\), every original \(e\mid m\) is such a divisor. The condition \(P^-(m)>z_*\) is **exactly** the independent conditions \(P^-(e),P^-(k)>z_*\), with \(P^-(1)=+\infty\), since the actual \(r\) is larger than \(z_*\). No extra rough restriction is imposed on \(q\) or on any of its divisors.

## 3. Short rough SW factor and genuine modulus slots

Open the \(h\)-score on \(d\mid q/p\), with original size \(d\le q^{.001}\). Again \(p\) exceeds all such divisors, so the opening is exact. This gives
\[
  Q=d s p,\qquad m=(r e) k\equiv N\pmod Q,\qquad (Q,N)=1.
\]
The short divisor \(d\), prime \(s\), and prime \(p\) are genuine independent modulus slots. The \(d\) and \(e\) weights are respectively \(\mu(d)h(\log d/\log q)\) and \(\mu(e)f(\log e/\log m)\); the outside \(\log m\) has canceled the \(r\)-tag denominator. For a size dyad \(e\asymp E\) put \(\epsilon_e=\log_x E\). If \(\nu=\log_x k\), then
\[
       \nu=1-\beta-\epsilon_e+o(1),\quad
       0\le\epsilon_e\le .001+o(1),\quad
       \nu>.001+\eta
\]
for some fixed \(\eta>0\) from (1). The long source factor is \(r e\). It has a unique actual \(r\) label because two such primes would have product \(>x^{1.818}\) while \(r e\ll x\). Both \(r e\) and \(k\) are restricted to be units at \(N\), as required by the actual \((m,N)=1\).

Here is the elementary Siegel–Walfisz check for the short factor \(k\) with the genuine roughness mask. For an interval in its dyad \(K\asymp x^\nu\), first count rough \(k\) with no Fourier twist. For any test modulus \(q_0\le L^B\) and reduced \(a_0\bmod q_0\), use the first \(J=\lceil C_A\log L\rceil\) Bonferroni layers for primes \(\ell\le z_*\) not dividing \(q_0\), with the last order adjusted to the two parities. Counting each CRT class uses its exact density and \(O(1)\) floor. The sum of floor errors is \(O((J+1) z_*^J)=x^{o(1)}\), negligible compared with a polynomial \(K\); the omitted density tails are \(O_A(L^{-A})\) using
\[
 \sum_{i\ge J-1}\frac{(\sum_{\ell\le z_*}1/\ell)^i}{i!}
                    \ll_A L^{-A}
\]
by taking \(C_A\) large and using the ordinary prime reciprocal estimate. All primes dividing \(q_0\) are below \(z_*\) for large \(x\), so the local product in its reduced class is exactly the full rough product divided by \(\varphi(q_0)\), when expressed per interval length. Consequently this agrees with \(1/\varphi(q_0)\) times the total rough count, to arbitrary log reserve. To include the extra coprimality mask to \(N\) and an auxiliary integer \(D_0\), discard \(k\) divisible by primes \(\ell>z_*\) dividing either of them; smaller ones are absent already. The error in both actual and model is bounded by \(O((\omega(N)+\omega(D_0))(K/z_*+1))\), within the allowed \(\tau(D_0)\) loss and arbitrary log reserve. For \(q_0>L^B\), counting all integers in the progression and bounding the modeled \(1/\varphi(q_0)\) term suffices. All these estimates hold uniformly for subinterval prefixes; partial summation therefore allows \(k^{it}\) with \(|t|\le L^{O(1)}\). This establishes Lichtman's condition (2.2), not only an unmasked mean over \(k\).

To absorb the continuous weights use the smooth endpoint and compact Fourier decomposition of [WrightSupercriticalPrimeProduct](WrightSupercriticalPrimeProduct.md), now in the normalized logs of \(s,d,e,m\). The product phase \(m^{it}\) separates on \(r e\) and \(k\); the log-\(e\) phase is part of the unique \(r e\) sequence, and the log-\(s,d\) phases are in their corresponding modulus coefficients. The literal factor \(W_s(q)/\log q\), \(q=(N-m)/s\), is kept in the continuous test throughout. The genuine \(\log p,\log r\) go on the prime modulus label and the long source respectively. Smooth derivatives, logarithmic cutoffs and the number of dyads cost only log powers. Normalize the prime log weights by \(O(L)\), or take out that factor explicitly. Every resulting coefficient is 1-bounded: \(k\) is a single rough-integer coefficient; \(r e\) has its unique \(r\) and then its unique \(e\); \(d,s,p\) are independent. No unproved extension to arbitrary divisor-order coefficients in Lichtman's result is needed. The interval smoothing loss is paid on actual rows by global divisor moments, and on the model similarly by the divisor-bounded \(m\) weights and \(\sum_{s,p,d}1/\varphi(s p d)\ll L^{O(1)}\). The use of \(z_*\) dominates all \(z_0(Y)=Y^{1/(\log\log Y)^3}\) in the cited theorem since every source dyad product \(Y\asymp x\).

Use [Lichtman arXiv:2309.08522v1, Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5), with \(Q_1\asymp d,\ Q_2\asymp s,\ Q_3\asymp p\) and short SW slot \(K\asymp k\); the \(d=1\) contribution is just the coefficient supported at 1 in its unit-size slot, permitted by the same inequalities. It is the proposition for three actual factor coefficients, not a theorem requiring this entire modulus sequence to be triply well-factorable at all factorizations. The residue \(a=N=2x\) is allowed uniformly by the printed \(0<|a|<Y^{1+\varepsilon}\), where \(Y\asymp x\). Let \(\delta=\log_x d\le .001\) before the \(o(1)\) endpoint allowances and \(\theta=7/32\) in this source's convention. The exponent conditions, with strict fixed reserve, are
\[
 \delta<\nu,\quad 2\nu+\sigma+2\alpha<1,\quad
 \theta+\nu+\delta+5\sigma+2\alpha<2,\quad
 2\theta(\nu+\alpha-\sigma)+\nu+\delta+5\sigma+2\alpha<2.
\]
The first two follow directly from (1). For the last two put \(B_1=\nu+\delta+5\sigma+2\alpha\). Then \(B_1<1+.001+4(.14)=1.561\), and \(2\theta(\nu+\alpha-\sigma)<\theta(1-3\sigma)\le.7\theta\). Both upper bounds have fixed positive room. Hence the proposition replaces the true sum by its actual coprime progression model with error \(O_C(xL^{-C})\), allowing all the preceding signed factors and Fourier separations.

## 4. The exact model is flat in the correct short modulus

Undo all dyads and smooth separations. Fix \(s,p,r,e,k\) in the original box with \(m=r e k\), \(q=(N-m)/s\) used only as a real variable in the model. Keep \((sp,Nm)=1\) and \((m,N)=1\); these are part of the model, not silent cancellations. Then \(d<s,p\), so \(\varphi(s p d)=\varphi(s p)\varphi(d)\), and the coprime condition on \(d\) is exactly \((d,Nm)=1\). The entire inner modeled \(d\)-sum is therefore
\[
  \frac{1}{\varphi(sp)}
   \sum_{(d,Nm)=1}\frac{\mu(d)}{\varphi(d)}
                      h\!\left(\frac{\log d}{\log q}\right).               \tag{3}
\]
The other smooth and arithmetic factors in this model, including every \(r,e,k\) rough gate and the \(f\)-weight, are independent of \(d\). The central endpoint is the same inside these real weights; \(d\) is restricted only by \(h\).

For completeness the inner harmonic in (3) is \(O_A(L^{-A})\) uniformly for the polynomial mask \(F=Nm\). Its Dirichlet series is \(\zeta(1+z)^{-1}E_F(z)\), where the local factor of \(E_F\) at \(\ell\nmid F\) is
\((1-\ell^{-z}/(\ell-1))/(1-\ell^{-1-z})\), and at \(\ell\mid F\) it is \((1-\ell^{-1-z})^{-1}\). The convolution coefficients of \(E_F\) have absolute mass \(L^{O(1)}\) at \(z=0\), and mass \(x^{o(1)}\) at \(z=-1/4\): the unmasked local differences are \(O(\ell^{-7/4})\) there, and the masked product is bounded by splitting primes at \(L\). For a cumulative harmonic up to \(y\ge x^\eta\), split that convolution at \(y^{1/2}\). The larger convolution tail is power-small by Rankin; on the smaller part use the ordinary Möbius harmonic prime number theorem with arbitrary log reserve. Finally partial summation against the exact derivative of \(h\), supported at \(d\ge x^{c(h)}\), gives the claim. In particular the normalization is \(\mu(d)/\varphi(d)\) here, not the \(\mu(d)/d\) used in the other orientation.

The outer \(\sum_{s,p}1/\varphi(sp)\) costs only log powers; at fixed \(m\) the remaining multiplicity of \(r,e,k\) and size of log weights cost bounded divisor powers and logarithms. Their absolute total is \(O(x L^{O(1)})\), so (3) cancels to arbitrary log reserve on the exact rough branch. Restoring precisely the omitted rows bounded in Section 2 proves (2).

This is a large true \(p<r\) region not controlled by the subcritical spectral product proof or by the narrow Wright boxes. It does not address \(r\) near \(x^{.51}\) with a genuine balanced semiprime \(q\): then \(k\) is too long for (1) and the prime-modulus factors cannot be split across these same rails. No bound on the rest of the signed ledger or on binary Goldbach is inferred.
