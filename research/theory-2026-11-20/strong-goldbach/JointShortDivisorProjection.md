# Both reflected and quotient largest-factor cutoffs at one target

This note gives two joint projections of the actual weighted semiprime–prime observable. The fixed smooth-score version also proves the nonzero intersection calibration in the centered ledger. A kernel-free version places both legs above an exact subpower roughness cutoff and removes the entire reflected semiprime row up to \(o(M_N)\). Both retain a signed higher-rank remainder; neither bounds it at the Goldbach threshold.

## 1. Statement and literal endpoints

Keep \(N=2x\), \(L=\log x\), \(M_N=\mathfrak S(N)x/(2L)\), the true prime \(x^{.10}<s<x^{.14}\), \(n=sq\in(x/2,x]\), \(m=N-n\), \((n,N)=1\), and \(W_s(q)=(1-t)(1-2t)^2\), \(t=\log s/\log(sq)\). Write \(Z_N=\sum_{s,q\text{ prime}}W_s(q)\Lambda(m)\). For \(B_j=x^{b_j}\), \(j=q,m\), let
\[
 T_q(q)=\sum_{d\mid q,\ d<q/B_q}\mu(d),\qquad
 T_m(m)=\sum_{d\mid m,\ d<m/B_m}\mu(d).                              \tag{1}
\]
Here \(b_q,b_m>1/2\) and are at most \(.51\). The strict endpoints are \(m<N-sB_qd\) on the quotient leg and \(n<N-B_md\) on the reflected leg. Both scores equal 1 on the corresponding prime, since \(q\gg x^{.86}\), \(m\ge x\). For a composite with a prime factor \(r>B_j\), no counted divisor can carry \(r\), because \(B_j^2>y\) for the corresponding argument \(y\), and **all** divisors of \(y/r>1\) lie below \(y/B_j\). The full Möbius sum on the cofactor is zero. Repeated primes in the cofactor do not change this proof.

For the fixed smooth version let \(h,f\) be the two affine-germ kernels of [UngatedReflectedRankProjection](UngatedReflectedRankProjection.md) with positive support limits \(c_h<b_q-1/2\), \(c_f<b_m-1/2\) and \(c_f<.001\). Define \(A_q(q)=H_h(q)\), \(A_m(m)=H_f(m)\) as there. One may instead take \(A_q=A_m=1\). With either choice and fixed cutoffs,
\[
 Z_N=\sum_{\substack{q,m\text{ composite}\\P^+(q)\le B_q,\ P^+(m)\le B_m}}
   W_s(q)(\log m) A_q(q) A_m(m)T_q(q)T_m(m)+O_A(xL^{-A}).             \tag{2}
\]
All sums include the literal true \(s\) wherever not displayed. In particular, the two one-leg nulls of the smooth composite ledger do **not** permit dropping their intersection: if \(X=W_s(q)(\log m)H_h(q)H_f(m)\), and \(\sum_c\) means both legs composite, then
\[
 \sum_c X(T_q-1)(T_m-1)=(J+o(1))M_N,
 \qquad J=\log(7/5)-.1408.                                           \tag{3}
\]
Thus the strict sufficient eventual threshold for the literal sum in (2) is \((J+.010)M_N\) with fixed margin, not \(.010M_N\). The centered ledger is still \(E_N=Z_N-(J+o(1))M_N\). There is no additional budget from a previous projection.

## 2. Joint CRT and the two single-prime distributions

Here is an argument that works both with short smooth divisor scores and with the two roughness approximants introduced later. At the opening stage put \(e_q,e_m\) for the least common multiples of any other fixed divisor labels on the two legs. On the nonzero Möbius support all these divisors are squarefree. These labels have absolute harmonic moments bounded by log powers: for each combined modulus the number of original labels is at most a fixed power of \(\tau\), and all coefficient weights have at most log-power size. For the fixed smooth case there is one such divisor per side and the size limits are \(e_q\ll q^{c_h}, e_m\ll x^{c_f}\). In the kernel-free and rough case they are respectively at most \(z_q^K,z_m^K\), specified in Section 4. The sums in this section use the original fixed sign/smooth functions of the labels, not arbitrary coefficients on the genuine prime slots.

For opened \(d_q,d_m\) in (1) set \(D_q=\operatorname{lcm}(d_q,e_q)\), \(D_m=\operatorname{lcm}(d_m,e_m)\). The all-integer model counts exactly the classes \(n\equiv0\pmod{sD_q}\), \(n\equiv N\pmod{D_m}\), \((n,N)=1\). It is empty unless \((sD_qD_m,N)=1\) and \((sD_q,D_m)=1\). The latter condition is forced because any common prime divides \(N\), contradicting the unit support. Otherwise the CRT density is \(\phi(N)/(NsD_qD_m)\) and the floor error is \(O(\tau(N))\) per tuple before smooth partial summation. Both moving endpoints are kept in its integral. The number of tuples in the fixed smooth case is
\[
 O\bigl(x^{2-b_q-b_m+c_h+c_f+o(1)}\bigr),
\]
by opening \(d_q\ll x/(sB_q)\) and summing \(1/s\). This is power-small relative to \(x\); in the kernel-free rough variant the exponent is \(2-b_q-b_m+o(1)<1\) with a fixed gap. In the resulting integral one may fix all labels other than \(d\) on a single leg. Write \(d=a k\) with \(a\mid e\), \((k,e)=1\) (the unique decomposition with \(a=(d,e)\), since \(d\) is squarefree). Then \(\operatorname{lcm}(d,e)=ek\), and the \(d\)-harmonic becomes \(\mu(a)\sum_{k<y/(B_j a),(k,K_0)=1}\mu(k)/k\), with the exact unit mask from the opposite labels, \(N,e\). The upper endpoint is polynomially long uniformly: for instance \(q/B_q\gg x^{.35}\), and \(a\le e\) has much smaller exponent. The masked harmonic is \(O_A(L^{-A})\) by the uniform finite Möbius PNT of the Ungated note, equation (4) proof before taking the derivative. The remaining absolute harmonic sums lose only log powers. Therefore the all-integer sum containing the full two \(T\)'s is zero to arbitrary log reserve.

For genuine prime \(q\), its own \(A_q T_q\) equals 1. Any roughness divisor on that leg is then necessarily 1 as well. Use the actual prime product \(n=sq\) in [Maynard's generalized BV, Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733), in the precise \(x^{1/2}/L^{C_A}\) form quoted and explained in [FullScaleConvolutionBV](FullScaleConvolutionBV.md). Both slots have polynomial length and genuine prime SW persists under the independent target masks, by deleting at most \(O(L)\) primes and partial summation. The modulus is the actual reduced \(D_m\), and its model is \(1_{(n,D_m)=1}/\phi(D_m)\), not just a freely chosen integer density. For the moving prefix and separated smooth tests use precisely the Shiu log meshes of [UngatedReflectedRankProjection](UngatedReflectedRankProjection.md), Section 2. The \(\tau(D_m)^C\) multiplicity is paid by Cauchy interpolation between the unweighted BV discrepancy and the uniform Shiu bound \(\ll x L^{O(1)}/\phi(D_m)\); the harmonic \(\tau^{2C}/\phi\) sum has log-power size. Undo the model's separations, fix actual \(s,q\) and the other \(m\)-leg label \(e=e_m\), and use the exact \(d=ak\) decomposition again. Now \(\phi(D_m)=\phi(e)\phi(k)\), and the finite masked harmonic \(\sum_{k< m/(B_m a),(k,Ns q e)=1}\mu(k)/\phi(k)\) is log-small uniformly (Goldston–Yıldırım as in [Huang–Li, Lemma 1](https://arxiv.org/pdf/2005.03811), with polynomial mask/endpoint). The summed prime-\(q\) contribution is therefore zero to arbitrary log reserve.

For genuine prime \(m\), its own score equals 1, and its roughness divisor, if any, is 1. Use ordinary maximal prime BV on \(m\equiv N\pmod {sD_q}\) with the literal prefix \(m<N-sB_qd_q\), \(\log m\) providing the prime Mangoldt log; proper prime powers contribute power-small error using the total divisor weight in \(N-m\). The weights have bounded variation up to fixed log powers. Again the weighted modulus multiplicity is paid by Cauchy interpolation with the trivial Shiu upper. In the resulting integral fix \(s,e=e_q\) and the continuous physical \(m\), put \(q=(N-m)/s\), and split \(d=ak\). If \(s\mid e\), \((k,e)=1\) suffices for \(\phi(s e k)=\phi(se)\phi(k)\). Otherwise the exact factor is
\[
 \frac{1}{\phi(s e k)}=\frac{1-s^{-1}1_{s\mid k}}{\phi(se)\phi(k)}.
\]
The extra \(s^{-1}\) contribution is power-small after absolute harmonic summation because \(s>x^{.10}\). The leading masked \(\mu(k)/\phi(k)\) harmonic is log-small. Again the full single-prime leg is null. All these analytic estimates hold whenever the reflected level \(D_m\) and the quotient level \(s D_q\) are below half by more than the required fixed logarithmic power.

On both primes the integrand is \(W_s(q)\log m\), exactly the original atom modulo proper prime powers in \(Z_N\), of total cost \(x^{1/2+o(1)}\). Inclusion–exclusion (whole integer minus each single-prime leg plus both primes) proves (2). On the fixed smooth ledger the original prime matching states \(\sum_c X=E_N+O_A(xL^{-A})\); both one-leg nulls are also valid. The reflected one is the centered-source argument in the Ungated note. For the quotient one keep \((\log m)(H_f-1_{m\text{ prime}})\) on the reflected side and drop the \(q\)-prime exclusion because \(T_q-1=0\) there. The same ordinary BV in \(A=s\operatorname{lcm}(d,a)\), now with \(d>1\), matches the integer \(f\)-score CRT principal with the prime one: at fixed \(A\), the density \(\phi(N)/(NA)\) multiplies \((\log m)\sum_{(e,NA)=1}\mu(e)f(\log e/\log m)/e=(NA)/\phi(NA)+O_A(L^{-A})\), giving \(1/\phi(A)\). The floor count exponent is \(1-b_q+c_h+c_f<1\). Combining these two nulls with (2) and the original \(E_N=Z_N-(J+o(1))M_N\) proves (3) without pretending the nulls multiply. The constant \(J\) is the actual \(\int_{.10}^{.14}(1-2t)^2\,dt/t\) calibration, not a new free error allowance.

## 3. Fixed smooth collar and its asymmetry

On a true reflected semiprime in (2), both factors are in \([x^{1-b_m},x^{b_m}]\), and \(T_m=H_f=1\). At fixed true prime \(r\) for one factor, the free affine forms of the Ungated note are \(q=q_0+rj\), \(v=(N-sq_0)/r-sj\), with true \(v\) the other prime. Majorize \(v\) by its \(x^{.4}\)-rough indicator, retain the unit masks, and use its explicit local factor calculation of \(\mathfrak S(N)\) at all primes including 2. Since \(|T_q|\le 2^{\omega(q)}\), double the old local Fourier majorant for \(|H_h(q)|\) at every prime power. This is still a uniform multiplicative Henriot weight, and the Euler cost \((1+|\xi|)^4\) is integrable against fixed smooth \(\widehat h\), rather than the old exponent 2. Thus the entire reflected semiprime contribution is \(O_h((b_m-.5)M_N)+O_A(xL^{-A})\) independently of \(f,b_q\). There is **no symmetric collar claim**: \(q\asymp x/s\), so \(B_q=x^{b_q}\) does not approach half-scale relative to \(q\) as \(b_q\downarrow.5\).

## 4. Kernel-free simultaneous roughness and moving reflected collar

Use now \(A_q=A_m=1\) and write \(T=\log L\) for the scalar only in this section. Fix \(b_q=.501\), put
\[
 b_m=.5+T^{-20},\qquad z_q=\exp(L/T^3),\qquad z_m=\exp(L/T^{23}),
 \qquad K=\lfloor T^2\rfloor .                                      \tag{4}
\]
Each of the two scores (1) is multiplied first by the corresponding Bonferroni polynomial \(R_j(y)=\sum_{e\mid y,\ P^+(e)\le z_j,\ \omega(e)\le K}\mu(e)\). By Section 2 all terms before the true both-prime atom still vanish to arbitrary log reserve. In fact \(Q_m=D_m\le(1.5x)x^{-b_m}z_m^K\ll x^{.5-T^{-20}+T^{-21}}\), which is below \(x^{1/2}/L^{C_A}\) for any fixed \(C_A\). Also \(sD_q\ll x^{1-b_q}z_q^K\) has a fixed power gap below half eventually. All modulus weights remain bounded by fixed divisor powers independently of growing \(K\), since there is just one chosen Bonferroni divisor per leg. Opening the two yields the all-integer exponent \(2-b_q-b_m+T^{-1}+T^{-21}+o(1)<1\) with a fixed gap eventually. Each moving endpoint in the harmonic calculation stays polynomially long, and the smooth meshes and fixed height reserves used before are uniform as \(b_m\downarrow.5\). Equation (2) thus holds with the inserted product \(R_q R_m\).

Let \(\rho_j(y)=1_{P^-(y)>z_j}\), where \(P^-(1)=\infty\). Consecutive Bonferroni inequalities give \(|R_j-\rho_j|\le\binom{\omega_{\le z_j}(y)}{K+1}\), and \(|R_j|\le\tau(y)\). Expand
\((R_q-\rho_q)R_m+\rho_q(R_m-\rho_m)\)
and bound the physical weighted error in (2) by divisor powers, using \(|T_qT_m|\le\tau(q)\tau(m)\). At a single opened error label \(e\mid y\), with \(K+1\) distinct small prime factors, write \(y=e u\) and use \(\tau(eu)^j\le 2^{j(K+1)}\tau(u)^j\) for the fixed needed powers. If the tagged leg is \(q\), the two forms are \(u,N-seu\); if it is \(m\), solve \(u\equiv N\overline e\pmod s\) and use \(u_0+s j,(N-eu_0)/s-ej\). Here \(e<x^{o(1)}\), its primes are smaller than \(s\), and all necessary \((se,N)=1\) masks follow from the actual unit condition. Cauchy–Schwarz and Shiu for fixed divisor powers on the two resulting primitive progressions give \(O(x L^C/(s e))\) at fixed \(s,e\), apart from \(2^{O(K)}\). Both affine progressions have fixed power reserve in size and modulus; one may drop prime and rank conditions only in this nonnegative upper. The harmonic sum of the error labels is at most
\[
 \frac{\bigl(C_0\sum_{p\le z_j}1/p\bigr)^{K+1}}{(K+1)!}
       \le \exp(-c T^2\log T),                                       \tag{5}
\]
including the \(2^{O(K)}\) factor by changing \(C_0\). This beats all fixed powers of \(L\). We have proved the analogue of (2) with both **literal** rough guards, to arbitrary log reserve. The true both-prime atom is unaffected.

Finally remove every surviving reflected semiprime. Its true prime factors \(r,v\) are both in \([x^{1-b_m},x^{b_m}]\), \(T_m=1\); on the quotient retain the actual \(\rho_q(q)\) and use \(|T_q(q)|\le2^{\omega(q)}\). With the same affine forms as in Section 3, take the multiplicative weight \(2^{\omega(q)}\rho_q(q)\) and the \(x^{.4}\)-rough upper for true prime \(v\). Corrected Henriot gives the original \(\mathfrak S(N)Y/L^2\) times the Euler envelope
\[
  \exp\left(2\sum_{z_q<p\le 2x}\frac1p+\sum_{x^{.4}<p\le 2x}\frac1p\right)
    \ll (L/\log z_q)^2=T^6 .
\]
The heights, prime masks, and local ratio are unchanged. The harmonic prime sum over \(r\) is \(O(T^{-20}+L^{-A})\); multiplying by \(\log m\) and summing the bounded \(1/s\) harmonic cost gives \(O(T^{-14}M_N)=o(M_N)\), including repeated equal primes. Squareful rows can also be removed to arbitrary log reserve in this rough support. At fixed \(s\), opening a square \(p^2\) with \(p>z_j\) costs at most \(O(x/(s z_j)+\sqrt{x})\) rows per leg in total. For the reflected leg \(p=s\) is impossible on the unit mask, and every other square gives one quotient residue class; on the quotient leg the same bound follows directly. Fixed moments of \(\tau(q)^C\tau(m)^C\) are \(O((x/s)L^{O(1)})\) by Cauchy and Shiu (the reflected progression is reduced modulo \(s\)). Cauchy with the support count therefore saves \(z_j^{-1/2}\), up to log factors and a power-small floor term, before the harmonic \(s\)-sum. This loses neither the kernel-free scope nor the Goldbach scale. The final statement is
\[
 \boxed{Z_N =
  \sum_{\substack{q,m\text{ squarefree composite},\ \Omega(m)\ge3\\
                  z_q<P^-(q)\le P^+(q)\le x^{.501}\\
                  z_m<P^-(m)\le P^+(m)\le x^{.5+T^{-20}}}}
       W_s(q)(\log m)T_q(q)T_m(m)+o(M_N).}                           \tag{6}
\]
No claim of polynomial roughness with fixed exponents is made. For squarefree composite \(m\), complementary divisors give the exact identity
\[
 2\,1_{\Omega(m)\,\mathrm{even}}T_m(m)
       =-\sum_{d\mid m,\ m/B_m\le d\le B_m}\mu(d).
\]
Indeed the strict low side of the cutoff and its complementary strict high side are disjoint, have signed ratio \(\mu(m)\), and together with the closed middle sum to 0. The signed composite remainder, including this even-rank central **integer** divisor collar, is not bounded by the semiprime argument: its harmonic label is not a genuine prime. The corresponding row signs still require fixed-target information. This is an unconditional support/roughness reduction for the literal \(Z_N\), not unconditional positivity of Goldbach.

## Related finite-sieve work

[Arneth, *Finite Bonferroni–Liouville Transfer* (October 22, 2026)](https://zenodo.org/records/23560521) already uses growing Bonferroni depth, factorial moments and divisor-square control in a different comparison for a prime-only source and a cube-root Liouville projector. Those truncation devices are not new here. The specific result above is an unconditional localization of the actual weighted prime-product observable after using both literal moving endpoints; it does not supply Arneth's coupled Liouville progression estimate. [Pham, *Uniformity, Local Structure and Boundary Correlations in Goldbach Representations* (October 30, 2026)](https://www.preprints.org/manuscript/202610.3061) analyzes another reflected boundary and separates unsigned character majorants from the signed target estimate; we do not use or claim to settle that estimate.
