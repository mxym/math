# A signed subfamily of the true reflected central-divisor band

This note bounds an actual fixed-target signed part of the central **integer-divisor** band from the kernel-free [JointShortDivisorProjection](JointShortDivisorProjection.md). The source in the difficult subtracted term is genuinely \(n=sq\) with *both* \(s,q\) prime. The increment is a signed cancellation, not an upper count by positive parts. It covers a specified family of raw band divisors, not the full band or a separately marked even-rank population.

## 1. Statement

Use \(N=2x\), \(L=\log x\), \(T=\log L\), \(M_N=\mathfrak S(N)x/(2L)\), \(x^{.10}<s<x^{.14}\) prime, \(n=sq\in(x/2,x]\), \(m=N-n\), \((n,N)=1\), and \(W_s(q)=(1-t)(1-2t)^2\), \(t=\log s/\log(sq)\). Keep the exact parameters of the kernel-free joint projection:
\[
 b_q=.501,\quad b_m=.5+T^{-20},\quad B_j=x^{b_j},\quad
 z_q=\exp(L/T^3),\quad z_m=\exp(L/T^{23}),\quad
 \rho_j(v)=1_{P^-(v)>z_j}.
\]
Write \(T_q(q)=\sum_{a\mid q,\ a<q/B_q}\mu(a)\). For a squarefree modulus \(d\), let \(d_0=\prod_{p\mid d,\ p\le x^{.010}}p\); the product is over its actual prime factors. Use the literal grouped family
\[
            \mathcal D=\{d:\ P^+(d)\le x^{.120},\quad d_0\ge x^{.088}\}.
\]
Then uniformly on every large even target,
\[
 \sum_{\substack{s\text{ prime},\ q\text{ composite}}}
 W_s(q)(\log m)T_q(q)\rho_q(q)\rho_m(m)
 \sum_{\substack{d\mid m,\ m/B_m\le d\le B_m\\d\in\mathcal D}}\mu(d)
       \ll M_N T^{-12}+O_A(xL^{-A}).                                \tag{1}
\]
The outer sum uses all original physical ranges above; it imposes no primality assumption on \(m\). The inner range is empty on prime \(m\), on every surviving true reflected semiprime (its eligible divisors are large primes), or whenever \(m\) has a prime above \(B_m\). The bound is absolute on the **signed total**, not termwise. For example the family includes the interior near-half profiles with about \(.09\) in primes of exponent below \(.01\) and about \(.41\) distributed among four primes of exponent near \(.1025\); eligibility is not the condition that the entire modulus is very smooth.

## 2. Reduction of (1) to the genuine prime-source band

First replace rough indicators by their ordinary Bonferroni polynomials of degree \(K=\lfloor T^2\rfloor\). The error estimate of JointShortDivisorProjection, Section 4, still applies: all coefficients at a row before the removal are bounded by fixed powers of \(\tau(q)\tau(m)\) times \(L\), since an extra raw divisor sum has size at most \(\tau(m)\). Thus the Cauchy–Shiu bound at a squarefree error label \(e\), followed by \((C_0\sum_{p\le z_j}1/p)^{K+1}/(K+1)!\), gives arbitrary log reserve, also whenever only the reflected replacement is made. This argument does not assume either leg has bounded rank.

Drop the \(q\)-composite condition temporarily. Open the true divisor \(a\mid q\) from \(T_q\), the two roughness labels, and \(d\mid m\) in the literal band. The number of tuples before CRT floors is at most
\[
       x^{1-b_q+b_m+T^{-1}+T^{-21}+o(1)}=x^{.999+o(1)},
\]
using the harmonic \(1/s\) from \(a\le x/(sB_q)\). The exact congruences are \(n\equiv0\pmod{s\operatorname{lcm}(a,e_q)}\) and \(n\equiv N\pmod{\operatorname{lcm}(d,e_m)}\), with both moduli units at \(N\) and coprime to one another. This is still below the product hyperbola with fixed reserve, even though \(d\) can exceed \(\sqrt x\). The elementary CRT principal disappears by the same fixed-label opening \(a=u v\), \(u\mid e_q\), \((v,e_q)=1\), with masked polynomial-endpoint \(\mu(v)/v\) harmonic zero as in the Joint note, Section 2. All moving endpoints, including the actual \(m\le B_m d\), remain in that integral. Hence the all-integer \(q\) part in (1) is \(O_A(xL^{-A})\).

It remains to bound the subtracted **true prime \(q\)** part. Here \(T_q=\rho_q=1\) exactly. Because of the literal \(\rho_m\), restrict \(P^-(d)>z_m\) before the Bonferroni opening on \(m\). The new label \(e\) has primes all \(\le z_m\), so \((d,e)=1\), and the actual modulus is \(d e\). It is not claimed that unstructured moduli in this band admit a super-half BV theorem.

## 3. Canonical dispersion rails for the complete family \(\mathcal D\)

For any squarefree \(d\in\mathcal D\) in the band, list its prime factors in increasing order. Take \(A\) to be the first prefix with product at least \(x^{.088}\), then \(D\) the next prefix with product at least \(x^{.116}\), and \(C\) the remaining product. The hypothesis \(d_0\ge x^{.088}\) is precisely the requirement that the first crossing uses only primes \(\le x^{.010}\). Thus if \(a=\log_x A\), \(b=\log_x D\), \(t=\log_x d\), \(\ell=\log_x e\), their exact restrictions are
\[
 .088\le a\le .098,\quad .116\le b\le .236,\quad
 .4999\le t\le .5001,\quad 0\le\ell\le .0001,\qquad
 \log_x C=t-a-b,                                                     \tag{2}
\]
for sufficiently large \(x\). The cutoffs ensure both prefixes exist and leave \(C\) polynomially long. The three actual modulus slots for [Lichtman, Proposition 5.2](https://arxiv.org/html/2309.08522v1) are \((A e,D,C)\). The slot \(Ae\) determines \(A,e\) uniquely by the cutoff \(z_m\). The \(N\)-slot of the proposition is the physical, genuinely SW prime \(s\) of exponent \(\sigma\in(.10,.14)\); the other slot is the physical prime \(q\). Both are 1-bounded after normalizing any extracted log factors. The SW property of \(s\) and its auxiliary unit masks follows as in the Joint note, and every modulus coefficient is supported on units at the **moving** residue \(2x\).

To check the four rails, use the actual correlation of dyadic exponents in (2), not independent worst bounds for \(C,D\). Up to dyadic errors \(o(1)\) their left-hand exponents with \(\vartheta=7/32\) are
\[
\begin{aligned}
 a+\ell&\le .0981<.10,\\
 2\sigma+2t-2a-b&\le .9882<1,\\
 \vartheta+\sigma+2t-a+3b+\ell&\le 1.97905<2,\\
 \sigma+2t-a+3b+\ell+2\vartheta(\sigma+t-a-2b)
     &\le1.79534375<2 .
\end{aligned}
\]
The last expression is increasing in \(\sigma,t,b,\ell\) and decreasing in \(a\); its bracket is positive throughout the listed range. All margins allow one fixed \(\epsilon\) in the proposition (e.g. \(.0004\)), and \(|2x|<x^{1+\epsilon}\) eventually.

The factorization is exact under recombination: require \(A/P^+(A)<x^{.088}\), \(D/P^+(D)<x^{.116}\), and the cross-order inequalities \(P^+(A)<P^-(D)\), \(P^+(D)<P^-(C)\). Each within-factor prefix check is part of that slot's coefficient. The signed weights \(\mu(A)\mu(D)\mu(C)\mu(e)\) are a pure product, and the cross-order checks are exactly separable by a finite Fourier expansion of \(1_{u<v}\) on the integer prime labels: embed the difference interval in a cyclic interval of twice the required length, then the Fourier coefficient \(\ell^1\) mass of the indicator is \(O(\log x)\). This includes equal boundary labels correctly and cannot introduce duplicate primes. Such modulus-slot phases have modulus 1 and do not change the SW source. Use dyads and log-relative meshes in the products and the two prime coordinates for the literal inequalities \(d\le B_m\), \(n\ge N-B_m d\), \(x/2<n\le x\), and smooth \(W_s(q)\log m\). At fixed \(d,e\) a changed physical prefix lies in an \(O(x L^{-F})\) strip, which costs \(O(x L^{-F+O(1)}/\phi(d e))\) by the same Shiu estimate as in the Joint note (\(d e<x^{.51}\) eventually). The changed \(d\)-band endpoints lie in relative \(O(L^{-F})\) strips around a polynomial \(d\) scale; summing their harmonic divisor weights gives \(O(L^{-F+O(1)})\). The analogous coprime model estimates hold. Thus finitely many log-power meshes and exact Fourier comparisons are paid by arbitrary log reserve in Prop. 5.2. Restoring the physical weights, moving endpoints, and the unique full family, its principal is the true sum over \(s,q\) prime with exact reduced weight \(1/\phi(d e)\). No well-factorable representation for other partitions is invoked.

## 4. The signed prime-source principal

At fixed true \(s,q\), every \(e\) is automatically coprime to \(s q\) and to \(d\). The exact principal splits into
\[
 \left(\sum_{\substack{e\ {
m squarefree},\; P^+(e)\le z_m\\\omega(e)\le K,\ (e,N)=1}}\frac{\mu(e)}{\phi(e)}\right)
 \sum_{\substack{m/B_m\le d\le B_m,\ (d,Ns q)=1\\P^-(d)>z_m,\ d\in\mathcal D}}\frac{\mu(d)}{\phi(d)} .              \tag{3}
\]
The first parenthesis agrees to arbitrary log reserve with \(\prod_{p\le z_m,p\nmid N}(1-1/(p-1))\), by the harmonic factorial Bonferroni estimate. The product is \(O(\mathfrak S(N)/\log z_m)\): compare with the dimension-one Mertens product, with odd-prime ratio \(p(p-2)/(p-1)^2\) for \(p\nmid N\) and ratio \(p/(p-1)\) when \(p\mid N\), and ratio 2 at the excluded prime 2. Missing larger factors from \(N\) only weaken the upper bound.

For the second sum fix the actual macro product \(d_1=d/d_0\), with primes in \((x^{.010},x^{.120}]\). Its reciprocal harmonic mass is bounded independently of \(x,N\), since \(\sum_{p\in(x^{.010},x^{.120}]}1/(p-1)=O(1)\). Retain the true mask \((d_1,Ns q)=1\) (in particular \(s\) can divide a macro product). The remaining \(d_0\) has no common prime with \(s q\), and ranges over its exact interval \([m/(B_m d_1),B_m/d_1]\cap[x^{.088},\infty)\), with prime factors in \((z_m,x^{.010}]\) and mask \((d_0,N)=1\).

We prove the needed signed harmonic bound for any such interval \([X_1,X_2]\):
\[
 \left|\sum_{\substack{X_1\le u\le X_2,\ (u,N)=1\\
            z_m<P^-(u)\le P^+(u)\le x^{.010}}}\frac{\mu(u)}{\phi(u)}\right|
 \ll \frac{(\log z_m)T^8}{L^2}\bigl(1+\log(X_2/X_1)\bigr).            \tag{4}
\]
All nonempty endpoints are between \(x^{.088}\) and \(x^{.501}\). The following elementary convolution supplies (4). Let \(y=x^{.010}\) and \(U=\exp(T^4)\). Start with \(\mu(u)1_{P^+(u)\le y,(u,N)=1}\), which is the Dirichlet convolution of \(\mu(a)1_{(a,N)=1}\) and \(1_{P^-(v)>y,(v,N)=1}\). For \(X\in[x^{.06},x^{.51}]\) its sum below \(X\) is \(O(XT^8/L^2)\). In detail, the uniform coprime ordinary Mertens bound at all \(w\ge U\) follows by convolving \(\mu\) with the indicator of integers supported on primes of \(N\). Split this convolution at \(\sqrt w\). The first part gives \(O(wT^C e^{-c\sqrt{\log w}})\) by the classical zero-free-region Mertens bound. The other part is \(O(wT^C e^{-(\log w)/(2T)})\) by Rankin at \(1/T\): the inverse product over \(p\mid N\), \(p\le L^2\), is at most \(T^C\) since \(p^{1/T}\le e^2\), and primes \(p>L^2\) are negligible by their \(O(L)\) cardinality. These bounds both provide arbitrary log reserve at \(U\); by partial summation, the finite masked harmonic \(\sum_{a\le U,(a,N)=1}\mu(a)/a\) has the same reserve (its complete Abel value is zero). The implied constants are uniform for the polynomial mask \(N\).

The convolution terms \(a>U\) are bounded by summing over \(v\) first and using that masked Mertens bound on \(U<a\le X/v\). This gives arbitrary log reserve, since \(\sum_{v\le X}1/v\ll L\). For \(a\le U\), the [Buchstab rough-number estimate](https://arxiv.org/abs/2306.03347) gives
\[
  \Phi(X/a,y)=\frac{X}{a\log y}\omega\left(\frac{\log(X/a)}{\log y}\right)
          +O\left(\frac{X}{aL^2}\right),
\]
uniformly on this compact exponent-ratio interval away from 1. The mask \((v,N)=1\) changes this by \(O((X/a)L/y)\), using only primes \(p\mid N,p>y\). The Buchstab function is Lipschitz on the relevant interval. Replacing its argument by \(\log X/\log y\) therefore costs \(O(XT^8/L^2)\), since \(\sum_{a\le U}(\log a)/a\ll T^8\). The retained constant multiplies the log-small finite harmonic at \(U\). The first error sums with cost \(\sum_{a\le U}1/a\ll T^4\). This proves the claimed signed smooth Möbius bound. It is a version of the standard friable Möbius/Buchstab convolution (compare [Lachand–Tenenbaum](https://docnum.univ-lorraine.fr/public/DDOC_T_2014_0189_LACHAND.pdf)); the explicit polynomial-mask and error uniformity used here are as just shown.

Next insert the factor \(u/\phi(u)\). The Euler convolution relative to the preceding masked smooth sequence has coefficients \(r(p^j)=-1/(p-1)\) for \(j\ge1\) at allowed primes and zero at forbidden primes, since \(1-(p/(p-1))p^{-w}=(1-p^{-w})(1-\sum_{j\ge1}p^{-jw}/(p-1))\). Its \(\sum |r(v)|/v^{3/4}\) is bounded. Splitting at \(v=x^{.01}\) therefore preserves \(O(XT^8/L^2)\) under the harmonic convolution, with the tail power-small by the trivial bound. Finally remove all primes up to \(z_m\) by the inverse Euler factors for this modified Möbius sequence: the harmonic coefficients have masses \((p-1)^{-j}\) at \(p^j\), \(p\le z_m,p\nmid N\). Their total is \(O(\log z_m)\). Rankin at \(1/\log z_m\) cuts these coefficients at \(x^{.01}\), with relative error \(O(e^{-cT^{23}})\), since replacing \((p-1)^{-1}\) by \(p^{1/\log z_m}(p-1)^{-1}\) changes the product by a bounded factor. The latter follows by bounding the difference by \(O((\log p)/(p\log z_m))\) and using the prime harmonic log sum. The even target excludes \(p=2\) throughout this inverse product. The sizes remaining after both convolutions are at least \(x^{.068}\), so all the uniform smooth bounds apply. We have a summatory bound \(O(X(\log z_m)T^8/L^2)\) for the \(u/\phi(u)\) weighted, rough and smooth masked Möbius sequence. Partial summation with \(1/u\) gives (4) at the literal endpoints.

Since \(\log(X_2/X_1)\le 2T^{-20}L\) on the moved neck, (3)–(4), summing the bounded macro harmonic and then the true prime source \(\sum_{s,q\text{ prime}}W_s(q)\log m\ll x\), give
\[
      O\left(\mathfrak S(N)x\,T^8 L^{-2}(1+2T^{-20}L)\right)
                =O(T^{-12}M_N).
\]
This proves (1). Throughout, the possibly different factorization \(d=d_0d_1\) is used **only after** restoration of the actual coprime principal; it is not offered as independent Lichtman modulus slots.

## 5. Scope and comparisons

On the squarefree reflected composite support the full raw band equals \(-2\,1_{\Omega(m)\,\mathrm{even}}T_m(m)\), as in the Joint note. Equation (1) permits deletion of the stated **raw-modulus part** from that exact full identity. An individual paired orientation condition \(d\in\mathcal D\) need not be symmetric under \(d\leftrightarrow m/d\), so odd ranks may contribute and cancel across the raw partition. We do not infer a small count on even-ranked rows with a smooth divisor, nor any estimate for the raw complement where \(P^+(d)>x^{.120}\) or \(d_0<x^{.088}\). In particular this is not cancellation of the entire reflected even-rank remainder.

[Pham, *The Restricted Chen Sieve*, Theorem D](https://www.preprints.org/manuscript/202611.0694) is a universal all-partitions support theorem; it does not give the selected actual prime-source sum (1). [Chan's November *Theorem (1+1.75)* preprint, Appendices A–C](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) asserts a .599 level for its stated finite coefficient families; no result for the arbitrary reflected band or for (1) is imported from that text. The present use of Lichtman employs one explicit ordered partition and a separately evaluated signed rough-smooth main term, not either wider hypothesis. No strong Goldbach result is asserted.
