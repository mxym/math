# A cusp-zero spectral cancellation inside the genuine double-high center

The elementary forward and reverse completion rails in [ReverseLargeTagShoulder](ReverseLargeTagShoulder.md) both miss the physical profile \((\log_x s,\log_x p,\log_x r)=(.139,.450,.545)\). We give an unconditional fixed-target cancellation on an open box containing it. The new step is to keep the **whole short determinant sequence** \(k s'-k's\) in a spectral large sieve, rather than using individual incomplete Weil bounds. The theorem concerns one signed portion of the actual double-high ledger, not its whole remainder.

## 1. Exact statement and unchanged physical weights

Keep the short \(.001\) kernels \(h,f\), \(h=1\) and \(f(t)=1-t\) near zero, and the raised \(a=.359,\ B=.499\) dual projection from the reverse note. In particular, \(N=2x\) is the actual even target, \(L=\log x\), \(x^{.10}<s<x^{.14}\) a true prime, \(n=sq\in(x/2,x]\), \(m=N-n\), \((n,N)=1\), and
\[
 X_h(s,q)=W_s(q)(\log m)H_h(q)H_f(m).
\]
For true primes \(p\mid q,\ r\mid m\) in
\[
             .425<\log_x p<.451,\qquad .522<\log_x r<.5455,              \tag{1}
\]
we prove, at each target, that
\[
 \sum_{s,q,p,r}X_h(s,q)\frac{\log p}{\log q}\frac{\log r}{\log m}
                  =O_A(xL^{-A})                                       \tag{2}
\]
for every fixed \(A>0\). All of the \(s\)-band is allowed. Both true tags are proper and above their short divisor scores, so they already force both legs composite. In this box \(p<r\); the reflected \(r\) is unique, whereas each true \(p\) is still counted with its own log weight when appropriate. No primality of an unmarked cofactor is asserted. In particular there is a region strictly outside both elementary completion rails, not a re-estimate of a previously canceled strip.

## 2. From the actual prime pair to a positive squared norm

Use the same endpoint smoothing and separation of the physical weights as in the forward completion note. To recap the arithmetic, open \(d\mid q,e\mid m\), \(\mu(d)\mu(e)\ne0,\ d,e\le x^{.001+o(1)}\), with \((d,e)=1\) and the literal unit masks at \(N,s,p,r\). Write \(q=p d g u\), expanding the unit factor into \(g\mid N\) with its sign. The \(g>x^{.0001}\) part costs \(x^{1-.0001+o(1)}\) by counting physical \(n\) divisible by \(g\) and using divisor powers at \(n,m\). At smaller \(g\), the true congruence for the free \(u\) modulo \(re\) is
\[
 u\equiv N\overline{s p d g}\equiv N_0\overline{s p d}\pmod {re},
 \qquad N_0=N/g .
\]
The last equality on the physical column uses \(g\mid N\) and \((g,re)=1\). **Cancel \(g\) now.** Later this permits harmless enlargement to integer moduli not required to be units at \(g\), and it leaves the Hecke factor \(N_0\) prime to the spectral level.

Use \(S,A,B,D,E,g\) for dyadic sizes of \(s,p,r,d,e,g\), where the letter \(B\) in §§2–5 is the **length** of the \(r\)-dyad, not the exponent cutoff .499. Their \(x\)-exponents are \(\sigma,\alpha,\beta,\delta,\epsilon,\gamma\). Poisson on \(u\) uses \(x/(s p d g)\), with all nonzero frequencies truncated at
\[
 T\asymp \frac{S A D B E g}{x}\,x^\zeta,\qquad \zeta=.0002 .
\]
A sufficiently high, fixed number of integrations pays the omitted tail by a power, even when the original endpoint smoothing costs fixed powers of \(L\). All the physical tests can be separated as in the forward note: Fourier first in compact \(\log(s/S)\), then (on each signed dyad in \(k\)) in the compact dyadic logarithm of \(|k|x/(s p d\,r e g)\). This separates \(k,s,p,r\) after extracting the Poisson size \(x/(S A D B E g)\). Two derivatives in these compact separation variables give logarithmic \(L^1\) normalization; all needed derivatives in the physical test are smooth with logarithmic bounds. The log weights of \(p,r\) stay on their respective genuine prime axes. With \(d,e,g\) fixed, it therefore suffices to control
\[
 \mathcal T=\sum_{p,r} b_p c_r
 \sum_{\substack{s\sim S\ {\rm prime}\\0<|k|\le T}}
       a_s z_k\, e_{re}(kN_0\overline{s p d})                            \tag{3}
\]
with independent 1-bounded coefficients, \(b_p,c_r\) supported on the genuine primes in the two dyads, and \((s,N)=1\). For the inner function extend it by zero unless \((r,d e s)=1,\ (p,r e)=1\); these hold on the true prime input, and its extension after canceling \(g\) is well-defined. Terms with \((s,e d)>1\) cannot occur by sizes.

Apply Cauchy **once over both** \(p,r\), retaining all their genuine weights on the outer norm \(\ll\sqrt{AB}\). The squared inner norm can be enlarged to all integers \(p,r\) within fixed nonnegative \(C_c^\infty\) dyadic majorants \(w_p(p/A),w_r(r/B)\) of their actual intervals. This only bounds a positive squared norm, never changes any prime on the signed row. Expand that norm in \((s,k),(s',k')\). Its exact diagonal contributes \(O(ABST)\). Completion in \(p\) on any other term gives the classical Kloosterman sum, with the standard convention \(S(u,v;c)=\sum_{b\bmod c}^{*}e_c(u b+v\bar b)\):
\[
 \frac A{re}\sum_{\ell\in\mathbb Z}
   \widehat w_p\!\left(\frac{\ell A}{re}\right)
 S(\ell,N_0\,\Delta\,\overline{d s s'};re),\quad
       \Delta=k s'-k's                                                    \tag{4}
\]
for \(s\ne s'\). For \(s=s'\) replace \(\Delta,\ ds s'\) by \(k-k',ds\). The common unit conditions are retained. Before using any trace formula the integer \(r\) ranges over \((r,d e s s')=1\) in (4). Put \(L_0=BE/A\); one may truncate \(|\ell|\le L_0 x^\zeta\) by smooth decay, taking a fixed sufficiently large derivative order. The scalar weight in \(r/B\), including \(A/(re)\), has each fixed normalized derivative bounded by
\[
 \ll \frac{A}{BE}(1+|\ell|/L_0)^{-C}
\]
for any fixed \(C\). These bounds are independent of \(\Delta\).

## 3. Exact cusp-zero level and coefficient control

For \(s\ne s'\) put \(Q=e^2 d s s'\), an integer (not presumed squarefree). Since \((r,e)=1\), factor (4) by CRT. Its \(r\)-factor is initially
\(S(\ell\bar e,N_0\Delta\overline{e d s s'};r)\), and changing the unit variable by the factor \(e\) makes it
\[
 S(\ell,N_0\Delta\bar Q;r)=S(N_0\Delta,\ell\bar Q;r).
\]
The last equality uses both interchange of Kloosterman arguments and the scaling identity \(S(a,b;r)=S(a u,b\bar u;r)\). The complementary factor modulo \(e\) is periodic in the unit \(r\bmod e\) (and may depend on \(\ell,\Delta\)). Expand it in characters \(\chi\bmod e\): each normalized coefficient is bounded by \(E\), by the trivial \(e\)-term bound for the Kloosterman sum, and there are at most \(E\) characters. After dividing each coefficient by \(E\) to make it 1-bounded, the net loss is \(O(E^2)\). No sparsity or uniformity of that periodic factor in \(\Delta\) is needed.

Use \(\Gamma_0(Q)\) with nebentypus \(\chi\) inflated from \(e\), and cusps \(\infty,0\) with \(\sigma_0=\bigl(\begin{smallmatrix}0&-1/\sqrt Q\\ \sqrt Q&0\end{smallmatrix}\bigr)\). These cusps are singular for this multiplier, as conjugating the parabolic translation by \(\sigma_0\) gives lower-right entry 1 modulo \(Q\). For \(\gamma=\bigl(\begin{smallmatrix}u&v\\Qw&r\end{smallmatrix}\bigr)\), the matrix \(\gamma\sigma_0\) has lower-left \(r\sqrt Q\), upper-left \(v\sqrt Q\), lower-right \(-w\sqrt Q\). Its determinant condition implies \(-w\equiv\bar Q\bar v\bmod r\), and \((r,Q)=1\). Summing over unit \(v\bmod r\) gives exactly
\(\chi(r)S(M,J\bar Q;r)\) (or conjugate \(\chi\) under the alternate multiplier convention), with \(M\) the infinity index and \(J\) the cusp-zero index. This also matches [Kaneko, equation (2.16)](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/5DCDC7B095189BEA1CA5D67F30993508/S2050509422000330a.pdf/div-class-title-motohashi-s-formula-for-the-fourth-moment-of-individual-dirichlet-span-class-italic-l-span-functions-and-applications-div.pdf), with the stated multiplier convention. It is the generalized Kloosterman sum on modulus \(r\sqrt Q\) in the Kuznetsov formula. This derivation is why the modulus \(r\) is allowed to average over **all integers** here, but only after the preceding honest Cauchy step.

For fixed \(s\ne s'\), the map from \(k,k'\) to the integer \(\Delta\) is injective. Indeed \(|k-k_1|\le2T<\min(s,s')\), so \((k-k_1)s'=(k'-k'_1)s\) forces both equalities. Also \(\Delta\ne0\). The strict inequality uses \(\alpha+\beta+\delta+\epsilon+\gamma+\zeta\le.9988+o(1)\) on (1). Thus after all the separated coefficients and the normalized \(e\)-character coefficients, the resulting \(\Delta\)-sequence on \(|\Delta|\asymp J_0\) has
\[
 \|b_\Delta\|_2\ll\min(T,\sqrt{J_0}),\qquad J_0\ll ST.
\]
This is the gain over treating each determinant separately. The sign of \(\Delta\) and of \(\ell\) can be fixed on separate dyads; simultaneous sign reversal of the classical Kloosterman arguments lets the infinity index be positive throughout.

## 4. The spectral estimate, including small Bessel parameters

Here are detailed normalization and bounds for a fixed unequal \(s,s'\), character, \(\ell\ne0\), and determinant block \(J_0<|\Delta|\le2J_0\). Use [Drappeau, Lemmas 4.4–4.5, Proposition 4.7 and Lemma 4.8](https://doi.org/10.1112/plms.12022), in the [primary author PDF](https://drappeau.perso.math.cnrs.fr/documents/divtm-siegel.pdf), for generalized Kuznetsov, its Bessel transforms and the spectral large sieves. Write
\[
 C_0=B\sqrt Q,\qquad
 X_0\asymp\frac{\sqrt{N_0 J_0|\ell|}}{C_0},\qquad
 \vartheta=7/64 .
\]
The geometric Kuznetsov sum is normalized by \(1/(r\sqrt Q)\); convert to the unnormalized sum by taking out \(C_0\) and multiplying the smooth test by \(r/B\). The spectral Fourier coefficients therefore appear as \(\nu_f(M)=\sqrt M\,\rho_{f,\infty}(M)\) and \(\sqrt{|\ell|}\rho_{f,0}(\pm|\ell|)\), with exactly the measures in Drappeau (4.15)–(4.19), not unsquared Whittaker coefficients.

For the variable determinant, write the Kuznetsov test in its Bessel argument \(y\asymp X_0\), with the physical weight evaluated at \(4\pi\sqrt{N_0|\Delta||\ell|}/(C_0 y)\). Take a compact smooth extension in \(\log(|\Delta|/J_0)\) and Fourier-expand there. The Fourier component at \(t_0\in\mathbb R\) has six fixed derivatives in \(y\) bounded by the physical weight bound from (4), times \(X_0^{-j}(1+|t_0|)^{-2}\); take two integration-by-parts derivatives in the compact logarithmic variable. Fourier expansion now gives a test **independent of \(\Delta\)** and simply twists its coefficients by \(e^{it_0\log(|\Delta|/J_0)}\), of modulus one. This validates taking the full spectral polynomial norm rather than a sum of individual spectral values. The support remains \(y\asymp X_0\), and the Fourier \(L^1\) integral is uniformly bounded by the same estimates.

Because \((N_0,Q)=1\), use the unramified inverse Hecke identity at infinity:
\[
 \nu_f(N_0j)=
  \sum_{b\mid(N_0,j)}\mu(b)\chi(b)
       \lambda_f(N_0/b)\,\nu_f(j/b),\qquad j=|\Delta|.
\]
It is Möbius inversion of the ordinary Hecke multiplication formula (see [Kaneko, equation (2.21)](https://doi.org/10.1017/fms.2022.33)); apply it directly to the Fourier-coefficient sequence, without dividing by a first Fourier coefficient. It is valid also on an unramified Hecke eigenbasis in the oldform spaces. The spectral positive norms are basis invariant, so take such a simultaneous orthonormal basis; on the continuous spectrum use the usual Hecke-diagonal Eisenstein data, where the unramified eigenvalues are the divisor sums of two unitary characters. The [Kim–Sarnak bound, with unitary character](https://annals.math.princeton.edu/2011/174-1/p18) gives \(|\lambda_f(N_0/b)|\le x^{\vartheta+o(1)}\); holomorphic and Eisenstein eigenvalues satisfy the same upper (in fact a stronger one). The same \(\vartheta\) bounds \(|\Im t_f|\). Each \(b\mid N_0\) restricts to a subsequence and reindexes \(j/b\), never increasing the \(\ell^2\) norm above \(\min(T,\sqrt{J_0})\). The number of such \(b\) is \(x^{o(1)}\). This deals with \((N_0,j)>1\) without requiring coprimality of the determinant with \(N_0\).

Both cusps have \(\mu(\mathfrak a)=1/Q\) in Drappeau's notation and the primitive conductor \(q_0\) of the character is at most \(e\). The actual sizes give
\[
  q_0 J_0/Q \ll \frac{A B g}{x}\,x^\zeta < x^{-.003+o(1)},
 \qquad
  q_0|\ell|/Q\ll \frac B{A S^2 D}\,x^\zeta < x^{-.07+o(1)}.
\]
Thus Proposition 4.7 on the regular spectrum gives \(O(U^2)\) times the squared coefficient norm on a spectral dyad of height \(U\ge1\), at either cusp. Use the correct parity weights \((1+|t|)^{\pm\kappa}\) there to cancel the parity factor of the Bessel transforms; for opposite-sign arguments the two weights cancel in the product. For the exceptional terms apply Lemma 4.8 at \(Y=1\); both its size terms are bounded by the same strict inequalities. It remains to take the Bessel weights outside those positive norms. Lemma 4.4 and Cauchy across the two cusps give, after summing dyadic regular heights, a regular transform factor \(O((1+|\log X_0|)(1+X_0^{3/2}))\), since its decay is at least \(U^{-3}\) while the paired sieve factor is \(O(U^2)\). For the exceptional spectrum the factor is \(O(1+X_0^{-2\vartheta})\). These statements hold as well for the logarithmic Fourier components just described. This derives the spectral bound using the trace formula, not a purported estimate for a fixed large residue progression.

On the full completion support \(X_0\ll x^\zeta\), by
\[
 X_0^2\asymp x^\zeta\,\frac{J_0}{ST}\frac{|\ell|}{L_0},
 \qquad Q\asymp S^2 D E^2 .
\]
The possible power cost of the regular transforms is at most \(3\zeta/2=.0003\). In the exceptional factor, small \(|\ell|\) is paid when summing the **absolute completion weights**: on \(|\ell|\asymp L_1\), these are at most a constant times
\((L_1/L_0)(1+L_1/L_0)^{-C}(1+(L_0/L_1)^\vartheta)\), summable over dyads, since \(\vartheta<1\). For the determinant dyad,
\[
 \min(T,\sqrt{J_0})\bigl(1+(ST/J_0)^\vartheta\bigr)
       \ll T(1+(S/T)^\vartheta),
\]
splitting at \(J_0=T^2\), using \(\vartheta<1/2\). Thus after summing the character, all nonzero \(\ell\), determinant dyads and unequal \(s,s'\), this part of the squared norm is bounded by
\[
 x^{o(1)+.0003}\,
      S^2\, (B\sqrt Q)\, x^\vartheta\, T\,E^2\,(1+(S/T)^\vartheta).
                                                                         \tag{5}
\]
The extra \(E^2\) is precisely the small-modulus CRT and character cost, not a suppressed level factor.

## 5. Remaining second-moment terms and total arithmetic exponents

The \(\ell=0\) contribution for all nonzero off-diagonal numerators can instead be bounded by Ramanujan sums. For each fixed nonzero integer \(C\) of polynomial size, \(\sum_{r\asymp B}|c_r(C)|\ll B\,\tau(C)\): open \(b\mid(C,r)\), and use that only \(b\le O(B)\) occur. The extra \(e\)-factor costs \(E\), canceled by \(A/(BE)\) in completion. Thus the total \(\ell=0\) off-diagonal squared norm is \(O(x^{o(1)} A S^2 T^2)\). There is no application of spectral theory to a zero Fourier mode.

For equal \(s=s'\) and \(k\ne k'\), the incomplete Weil bound at one integer modulus \(re\) is \(\ll x^{o(1)}\sqrt r E\sqrt{(r,N_0(k-k'))}\), since \(A<B\) and the short coprime inverses do not alter the gcd. Averaging that gcd across all \(r\asymp B\) costs only \(x^{o(1)}\), by opening its divisors and \(\sum_{b\mid C,b\le2B}\sqrt b(B/b+1)\ll B\tau(C)\). There are \(O(ST^2)\), rather than \(O(S^2T^2)\), of these pairs, so their complete contribution to the squared norm is \(x^{o(1)} S T^2 B^{3/2}E\). This can include \(\ell=0\) as an upper; one may retain the previous separate bound just for unequal \(s\).

Pay for \(\mathcal T\) by \(\sqrt{AB}\) times the square root of these norm contributions and the true diagonal \(ABST\), then \(x/(S A D B E g)\) from Poisson and \(D E\) for summing the opened short divisors. The \(g\)- and dyad counts lose \(x^{o(1)}\). With
\(t=\sigma+\alpha+\beta+\delta+\epsilon+\gamma-1+\zeta\),
the resulting exponents are:
\[
 \begin{array}{c|l|c}
 \text{term}&\text{final exponent (up to }o(1)\text{)}&
                 \text{upper on (1)}\\ \hline
 \text{exact diagonal}&1+(\alpha+\beta+\delta+\epsilon-1-\gamma+\zeta)/2&.99935\\
 \text{same }s,\ k\ne k'&
 \alpha/2+5\beta/4+\sigma/2+\delta+3\epsilon/2+\zeta&.980075\\
 \text{unequal }s,\ \ell=0&
 \sigma+\alpha+\beta/2+\delta+\epsilon+\zeta&.86595\\
 \text{spectral unequal }s&
 \tfrac12+\sigma+\beta/2+3\delta/4+2\epsilon-\gamma/2
 +\zeta/2+\tfrac{\vartheta}{2}(1+\sigma-t)+.00015&<.974 .
 \end{array}
\]
For the last inequality \(\sigma-t\le1-\alpha-\beta\le .053\). All ceilings are strictly below 1 even retaining both .001 short divisors and .0001 unit cutoff. Choosing a sufficiently small power tolerance in the primary spectral estimates and in the tail separations leaves fixed room. This proves a power-saving nonzero Poisson error at each target.

Finally the original **true prime** zero frequency is unchanged from BalancedLargeTagTaper: it is the geometric CRT density with the unit factor \(\phi(N)/N\), and the bivariate coprime \(\mu/d,\mu/e\) harmonic vanishes to arbitrary log reserve by exact flatness of \(h\) and the absolutely Rankin-convergent short coupling Euler factor. The auxiliary integer enlargements were only inside the nonzero squared norm, never in that principal or on the original prime row. This proves (2).

For the combined projected criterion, subtract first the published disjoint elementary strips (and their chosen subcritical piece) and then the intersection of (1) with what remains. In particular there is a fixed open subbox around \((.139,.450,.545)\) genuinely beyond both elementary rails, so (2) advances that previously uncovered case. The support outside (1), notably configurations with \(\alpha+\beta\) beyond the power-saved diagonal threshold, is not estimated by this result. The \(.010 M_N\) upper on the rest of the actual signed ledger and the Goldbach conclusion remain open.
