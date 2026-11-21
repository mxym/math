# The full subcritical true prime-product sector

The [central spectral result](SpectralCentralDoubleHigh.md) was restricted to a small independent box. The short determinant and the nonzero completion frequency can both be kept as coefficient sequences in the spectral large sieve. A separate spectral estimate when the two source primes are equal then extends the result to the **whole coupled sector** below a fixed subcritical product cutoff.

## 1. Statement

Keep the physical setting and short kernels of [ReverseLargeTagShoulder](ReverseLargeTagShoulder.md): \(N=2x\) is even, \(L=\log x\), \(s\) is prime with \(x^{.10}<s<x^{.14}\), \(n=sq\in(x/2,x]\), \(m=N-n\), \((n,N)=1\). Let \(h,f\) be smooth, with support on nonnegative arguments at most \(.001\), with \(h(t)=1\) and \(f(t)=1-t\) in some fixed neighborhood of zero. As in the prior notes put
\[
 H_j(u)=\sum_{d\mid u}\mu(d)j(\log d/\log u),\qquad
 X_h(s,q)=W_s(q)(\log m)H_h(q)H_f(m),\qquad
 M_N=\frac{\mathfrak S(N)x}{2L}.
\]
The weight \(W_s(q)=W(\log s/\log(sq))\) has \(W(t)=(1-t)(1-2t)^2\). Uniformly at every sufficiently large even \(N\), for every fixed \(C>0\),
\[
 \sum_{\substack{\text{physical }s,q\\
                  p\mid q,\ r\mid m\text{ true primes}\\
                  p>x^{.359},\ r>x^{.499},\ pr\le x^{.997}}}
 X_h(s,q)\frac{\log p}{\log q}\frac{\log r}{\log m}
       \ll_{C,h,f} xL^{-C}.                                           \tag{1}
\]
Each true prime divisor is counted once with its own written log weight. Here \(p\le x^{.498}<x^{.499}<r\); both tags are proper, \(p<r\) always, and \(q,m\) are already composite. No statistical independence of any factor labels is used.

By the existing exact two-leg log-conservation identity at \(a=.359,B=.499\), this removes the entire \(pr\le x^{.997}\) portion of the doubly high signed remainder in that ledger. Its complementary portion still needs the actual signed upper bound \(<.010M_N\) with strict room. There is no conclusion about binary Goldbach from (1) alone.

## 2. Coupled boundary and signed norm

Let \(\rho=L^{-K}\) with \(K\) fixed as large as needed. Independently mesh the \(p\) and \(r\) intervals with relative widths \(O(\rho)\) (there are \(O_K(L^{K+1})\) intervals per axis), retaining interior rectangles below \(pr=x^{.997}\). Omitted crossing rectangles meet \(\lvert pr/x^{.997}-1\rvert\ll\rho\). We justify their removal **before** separating the tags.

For fixed physical \(p,r\), \(p,r\) are distinct units at \(N\); choose \(t_0\) with \(0<t_0<r\) and \(pt_0\equiv N\pmod r\). All candidate rows \(n=pt\), \(m=rv\) have \(t=t_0+rj\), \(v=(N-pt_0)/r-pj\). In any subinterval of \(n\)-length \(Y\), this gives a \(j\)-interval of length \(Y/(pr)\). Open both scores absolutely; each active divisor satisfies \(d\le q^{.001}\le x^{.001}\) and \(e\le m^{.001}\le (1.5x)^{.001}\). Since \(s\mid t\), \(d\mid q=t/s\) implies \(d\mid t\). The imposed unit condition \((n,N)=1\) forces \((t,v)=1\), so only \((d,e)=1\) are possible. With \(d,e<\min(p,r)\), the two divisibilities determine a single class of \(j\pmod {de}\). Once these incompatible pairs have been discarded, we may drop the unit condition in the positive upper count. There are at most 10 prime possibilities \(s>x^{.10}\) dividing \(t\le x\); no distribution of \(s\) is needed for this bound. Since all other weights cost \(O(L)\), the absolute bound on the original row is
\[
 \ll_{h,f} L\left(\frac{Y}{pr}L^2+x^{.002}\right).                     \tag{2}
\]
The total of the floor terms over any tag region \(pr\ll x^{.997}\) is \(O(x^{.999}L^{O(1)})\), summing dyads (or the elementary divisor summatory bound). For the crossing rectangles, sum the \(Y=x\) part first over \(r\); the ordinary effective prime number theorem gives uniformly, for polynomial \(R\asymp x^{.997}/p\),
\[
 \sum_{r\ \mathrm{prime},\ |r/R-1|\ll\rho}\frac1r
       \ll \rho/L+\exp(-c\sqrt L).
\]
This follows by subtracting the endpoint PNT formulas for \(\pi\) at the two endpoints and dividing by a comparable \(R\); no prime distribution in a power-short interval is invoked. The outer prime harmonic sum over \(p>x^{.359}\) is bounded. Thus the crossing terms are \(O_C(xL^{-C})\) by increasing \(K\). Formula (2) also permits independent smoothing of the two \(n\)-endpoints in intervals of length \(O(\rho x)\): the first part now sums to \(O(x\rho L^3)\) because both prime harmonic masses are bounded. All physical weights with \(n,m\) in a fixed central neighborhood have the same bounds.

On each independent \(p,r\) rectangle and size dyad, use the arithmetic and smooth Fourier separation of [SpectralCentralDoubleHigh](SpectralCentralDoubleHigh.md), Sections 2–3. In detail, open the two actual scores with squarefree \(d,e\), discard incompatible \((d,e)>1\), preserve \((de,Ns p r)=1\) and the true \(s,p,r\) unit tests. Expand the remaining \((n,N)=1\) as \(\sum_{g\mid(n,N)}\mu(g)\); the \(g>x^{.0001}\) part costs \(x^{1-.0001+o(1)}\) by counting \(g\mid n\) with divisor-power weights. For smaller \(g\mid N\), \(q=p d g u\), the exact free congruence is \(u\equiv N_0\overline{s p d}\pmod {r e}\), \(N_0=N/g\), after canceling \(g\) on the true prime support. Poisson extracts \(x/(S A D B E g)\), where \(S,A,B,D,E\) are the dyadic sizes of \(s,p,r,d,e\). As in the cited proof, use a compact Fourier expansion in the logarithm of \(s/S\) and a second one for the nonzero Fourier argument \(kx/(s p d r e g)\) on signed \(k\)-dyads. The physical functions vary smoothly only in these logarithms and the normalized \(n\)-variable; every needed fixed derivative costs \(L^{O(1)}\). Their compact Fourier coefficients have \(L^1\) loss \(L^{O(1)}\) by taking two derivatives. The independent indicator intervals in \(p,r\) stay in their prime coefficients and need not be smoothed.

Write the dyadic size exponents as \((\sigma,\alpha,\beta,\delta,\epsilon,\gamma)\) for \((S,A,B,D,E,g)\). Fixed constants in these sizes and in support loss below allow \(o(1)\) in the exponents. With \(\zeta=.0002\), truncate at
\[
 T=\frac{S A D B E g}{x}x^\zeta,\qquad
 t=\log_x T=\sigma+\alpha+\beta+\delta+\epsilon+\gamma-1+\zeta.
\]
A fixed sufficiently large derivative order pays the tail even after summing all dyads and opened moduli. If \(T<1\) there are no frequencies. Otherwise \(t\ge0\) and \(T<x^{-.0007+o(1)}S\). The reduction, with \(d,e,g\) fixed and all separation coefficients divided by their uniform bounds, is to 1-bounded independent coefficients in
\[
 \mathcal T=\sum_{p,r} b_p c_r\sum_{s\sim S\ \mathrm{prime}}
       \sum_{0<|k|\le T}a_s z_k e_{re}(kN_0\overline{s p d}).
\]
The literal \(p,r\) coefficients are prime supported. Apply Cauchy to \(p,r\) jointly, with outer norm at most \(\sqrt{AB}\); only in the positive squared norm may the \(p,r\) ranges be enlarged to integer dyads with fixed smooth majorants. Preserve the masks \((r,e d s)=1,(p,re)=1\) in the inner function. Its expansion has exact \((s,k)=(s',k')\) diagonal \(O(ABST)\). Completing \(p\) off that diagonal gives
\[
 \frac A{re}\sum_\ell\widehat w_p(\ell A/(re))
       S(\ell,N_0\Delta\overline{d J_s};re),
 \quad
 (J_s,\Delta)=
 \begin{cases}
 (s s',k s'-k' s)&s\ne s',\\
 (s,k-k')&s=s'.
 \end{cases}                                                          \tag{3}
\]
For \(s\ne s'\), the map \((k,k')\mapsto\Delta\) is injective and \(\Delta\ne0\), because \(|k-k_1|\le2T<\min(s,s')\) and the source primes are distinct. For the same \(s\), the \(k\ne k'\) terms have \(\Delta\ne0\) and multiplicity \(O(T)\) per integer \(\Delta\).

Set \(F_0=BE/A\), where \(B\) in this proof is the \(r\)-dyad size. Truncate completion at \(|\ell|\le F_0x^\zeta\); smooth decay gives an arbitrarily small tail by taking a fixed large derivative order. The scalar weight of (3), including the enlarged \(r\)-majorant, has normalized derivatives bounded by \(O_{j,D_1}(F_0^{-1}(1+|\ell|/F_0)^{-D_1})\) for any fixed derivative order \(j\) and decay order \(D_1\). The off-diagonal \(\ell=0\) contribution is \(O(x^{o(1)} A S^2 T^2)\), just as before: the \(e\)-factor has size at most \(E\), and \(\sum_{r\sim B}|c_r(C_0)|\ll B\tau(C_0)\) for each nonzero polynomially bounded determinant numerator (open divisors of the gcd).

## 3. Keeping both unequal-source indices in the sieve

Put \(Q=e^2dJ_s\). For each unit \(u_0\pmod e\), first restrict to \(r\equiv u_0\pmod e\); the \(e\)-part of (3) then equals
\[
 \sum_{y\bmod e}^{*}
       e_e(\ell\overline{u_0}y)\,
       e_e(N_0\Delta\overline{d J_s u_0}\bar y).
\]
This splits **as a function of the two indices** for each \(u_0,y\), as a single product of two phases. Expand the residue restriction in all characters modulo \(e\) with coefficient \(\overline\chi(u_0)/\phi(e)\). Summing absolute coefficients over \(u_0,y,\chi\) costs just \(\phi(e)^2\le E^2 x^{o(1)}\); both individual index weights have modulus one. The classical \(r\)-factor is \(S(N_0\Delta,\ell\bar Q;r)\) by CRT and inverse scaling, and the modulus is \(r\sqrt Q\) for the singular cusp pair \((\infty,0)\) of \(\Gamma_0(Q)\) with this character. This exact cusp matrix and nebentypus normalization, the normalized coefficients \(\sqrt n\rho_{\mathfrak a}(n)\), and the conversion factor \(B\sqrt Q\) for the unnormalized modulus average are derived in Sections 3–4 of the central spectral proof. In particular \((N_0,Q)=1\). Use the unramified Hecke inverse to peel \(N_0\) from the infinity index, with cost \(x^{\vartheta+o(1)}\), \(\vartheta=7/64\), including the divisor reindexing of its coefficient sequence proved there.

Fix signed dyads \(|\Delta|\asymp J,|\ell|\asymp F_1\). When the two source primes are unequal, the \(\Delta\) coefficients have \(\ell^2\) norm \(\ll\min(T,\sqrt J)\), \(J\ll ST\). The \(\ell\) coefficients have norm \(\ll\sqrt{F_1}\). To use both simultaneously, write the physical \(r\)-weight from (3) as a test in the Bessel argument \(y=4\pi\sqrt{N_0|\Delta||\ell|}/(r\sqrt Q)\). Its smooth Fourier expansions in **both** compact variables \(\log(|\Delta|/J),\log(|\ell|/F_1)\) yield tests independent of either index. On their common support
\[
 y\asymp X_0,\quad X_0^2\asymp x^\zeta\frac{J}{ST}\frac{F_1}{F_0}.
\]
The six normalized \(y\)-derivatives of each test are bounded by
\[
 \ll F_0^{-1}(1+F_1/F_0)^{-D_1}(1+v_1^2)^{-1}(1+v_2^2)^{-1}
\]
where \(v_1,v_2\) are the Fourier parameters. Indeed the smooth \(r\)-weight and its normalized derivatives at comparable \(r/B\) retain rapid decay in \(F_1/F_0\); differentiating in the two compact variables only inserts fixed extra normalized weight derivatives, and two integrations in each variable give an integrable envelope. The extra factor \(r/B\) for the unnormalized modulus average is a bounded smooth factor. Thus the integrations cost no length exponent, and the indices are twisted by unit-modulus factors in their respective coefficient norms.

Precisely, [Drappeau’s Proposition 4.7 and Lemmas 4.4–4.5 and 4.8](https://drappeau.perso.math.cnrs.fr/documents/divtm-siegel.pdf) apply as in the central proof. At either cusp \(\mu(\mathfrak a)=1/Q\) and the primitive character conductor \(q_0\le e\). For the infinity sequence \(q_0J/Q\ll ABg x^\zeta/x<1\) by a fixed power, also after the Hecke divisor reindexing. For the zero cusp allow the full factor \((1+E F_1/Q)^{1/2}x^{o(1)}\) in its norm. For the regular spectrum this follows by weakening the source's \(q_0^{1/2}\) to \(E\) and factoring out the spectral-height factor; for exceptional terms apply Lemma 4.8 with \(Y=1\) and use
\[
 (1+(F_1/Q)^{1/2})(1+(q_0 F_1/Q)^{1/2+\varepsilon})
            \ll_{\varepsilon}x^{O(\varepsilon)}(1+E F_1/Q).
\]
Cauchy in the regular spectral norm at height \(U\) costs \(O(U^2)\) for the pair of cusps, with the actual parity weights canceled against their Bessel transforms as in the central proof. Summing heights against the \(U^{-3}\) transform decay costs at most \(x^{.0003+o(1)}\) since \(X_0\ll x^\zeta\). The exceptional transform is at most \(O(1+X_0^{-2\vartheta})\). This treats both signs and the holomorphic, Eisenstein and Maaß contributions with the same source normalizations.

For the determinant dyads,
\[
 \min(T,\sqrt J)(1+(ST/J)^\vartheta)\ll T(1+(S/T)^\vartheta).
\]
For the nonzero completion dyads their total norm and weight loss is bounded, up to \(x^{o(1)}\), by
\[
 \sum_{F_1} \frac{\sqrt{F_1}}{F_0}(1+F_1/F_0)^{-D_1}
           (1+(F_0/F_1)^\vartheta)\sqrt{1+E F_1/Q}
 \ll F_0^{-1/2}+(E/Q)^{1/2}.
\]
Both assertions follow by splitting at \(J=T^2\) and \(F_1=F_0\), respectively, using \(\vartheta<1/2\). Therefore the unequal-\(s\), nonzero-\(\ell\) squared norm is bounded by
\[
 x^{.0003+o(1)}S^2 B\sqrt Q\,x^\vartheta T E^2
       (1+(S/T)^\vartheta)\bigl(F_0^{-1/2}+(E/Q)^{1/2}\bigr),
 \qquad Q\asymp E^2 D S^2.                                             \tag{4}
\]
The gain in (4) comes from two separate spectral coefficient norms, not presumed random signs or separate individual estimates for the \(\ell\) terms.

## 4. Equal sources and simultaneous totals

When \(s=s'\) and \(k\ne k'\), use exactly the same conductor argument with \(J_s=s\), \(Q=e^2 d s\), and \(\Delta=k-k'\). One may fix \(\ell\), keeping only the compact determinant Fourier separation, and sum its completion weights absolutely. The determinant sequence has norm \(\ll T\sqrt J\), \(J\ll T\). Here
\[
 X_0^2\asymp x^\zeta(J/T)(F_1/F_0),\qquad
 q_0J/Q\ll ABgx^\zeta/x<1.
\]
The exceptional determinant loss costs at most \(O(T^{3/2})\), since \(T\sqrt J(1+(T/J)^\vartheta)\ll T^{3/2}\). The singleton \(\ell\) norm in the spectral sieve is \(\ll x^{o(1)}(1+E F_1/Q)^{1/2}\). Now absolute completion weights contribute \(F_1/F_0\), not \(sqrt{F_1}/F_0\). Summing dyads using the same rapid decay costs at most \(O(1+(E F_0/Q)^{1/2})\). Thus the equal-\(s\) off-diagonal, nonzero-\(\ell\) squared norm is
\[
 \ll x^{.0003+o(1)} S B\sqrt Q\, x^\vartheta T^{3/2} E^2
                           (1+(E F_0/Q)^{1/2}),
 \qquad Q\asymp E^2 D S .                                              \tag{5}
\]
In particular a separate incomplete Weil bound is unnecessary for these terms.

Combining the exact diagonal, zero-completion off-diagonal, (4) and (5), multiply their square roots by the outer \(\sqrt{AB}\), then by the Poisson normalization \(x/(S A D B E g)\) and the opened-divisor count \(DE\). The resulting four exponents before \(o(1)\) are, writing \(u=\min(\beta+\epsilon-\alpha,2\sigma+\delta+\epsilon)\),
\[
 \begin{array}{c|l}
 \text{term}&\text{exponent}\\ \hline
 \text{exact diagonal}&1+(\alpha+\beta+\delta+\epsilon-1-\gamma+\zeta)/2\\
 \ell=0\ \text{off diagonal}&\sigma+\alpha+\beta/2+\delta+\epsilon+\zeta\\
 \text{spectral unequal}&
 \tfrac12+\sigma+\beta/2+3\delta/4+2\epsilon-\gamma/2
 +\zeta/2+\tfrac{\vartheta}{2}(1+\sigma-t)+.00015-u/4\\
 \text{spectral equal}&
 \tfrac14+\sigma/2+\alpha/4+3\beta/4+\delta+9\epsilon/4-\gamma/4
 +3\zeta/4+\tfrac{\vartheta}{2}+.00015
 +\tfrac14\max(0,\beta-\alpha-\sigma-\delta).
 \end{array}                                                           \tag{6}
\]
These are simultaneously less than (1) with a fixed reserve: the first is \(\le .9996\), the second \(\le .8897\). For the unequal expression, the macroscopic part of the two branches is at most
\(\tfrac12+\sigma+(\alpha+\beta)/4\le .88925\) or
\(\tfrac12+\sigma/2+\beta/2\le .889\), respectively. Since \(0\le t<\sigma\le .14\), all remaining terms leave it \(<.955\). For the equal expression, the macroscopic part is at most \(.88825\) in the zero branch or
\(.25+\sigma/4+\beta\le .923\) in the positive branch. The remaining terms leave it \(<.982\). The accompanying rational checker verifies these ceilings, the coefficient algebra and the fixed pre-truncation reserves. The finitely many smooth derivatives, divisor counts, and logarithmic number of Mellin and size dyads incur only \(x^{o(1)}\), or an arbitrarily small fixed power in the cited spectral sieves. Therefore the total nonzero Poisson error power-saves.

Finally, the original **true-prime** zero Poisson density was not altered. For each \(s,p,r\) individually, it is the geometric integral times the joint coprime \(\mu(d)/d,\mu(e)/e\) harmonic and the factor \(\phi(N)/N\), as in Section 4 of [BalancedLargeTagTaper](BalancedLargeTagTaper.md). The bivariate absolutely Rankin-convergent coprimality correction followed by the uniform coprime Möbius PNT in the \(d\)-leg gives arbitrary log reserve because \(h\) is exactly flat near zero; the \(e\)-leg only needs a harmonic upper bound. The truncated \(g\) tail in the density has the same power saving as a direct \(g^{-1}\) harmonic estimate. This completes (1) after restoring all independent rectangles and accounting for (2).

At or beyond \(pr\asymp x\) the exact squared-norm diagonal in (6) no longer saves a power, even though the spectral off-diagonal analysis is much stronger over parts of that larger region. In the physical fixed-\((p,r)\) parametrization the \(j\)-interval then has bounded length. The present theorem does not bypass that diagonal or control the remaining signed contribution.
