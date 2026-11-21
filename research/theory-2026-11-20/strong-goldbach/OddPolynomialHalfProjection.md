# A cubic half-projection on all odd reflected ranks

This is a different exact projection of the same actual `Z_N` as [JointShortDivisorProjection](JointShortDivisorProjection.md). A reflected cubic hinge removes the entire unbounded odd reflected rank range and the giant-prime range, leaving smooth even ranks and a genuine favorable prime–prime-product term. The new calibration is **six times** the previous reference, not the previous threshold or a free reserve. An exact angular identity explains why reducing this calibration within the odd polynomial family creates adverse odd ranks.

Related work: [Arneth’s October 2026 cubic prime minorant](https://zenodo.org/records/23477014) also uses cubic weights in a Goldbach reduction, but uses a combination of generalized von Mangoldt functions on a shifted-prime source and makes its remaining signed correlation conditional. Here the cubic is a half-divisor polynomial on the reflected factor simplex; its odd-rank and angular identities concern a different score.

## 1. Statement and calibration

Keep the true even target \(N=2x\), \(L=\log x\), \(T=\log L\), \(\Delta=T^{-20}\), \(B_q=x^{.501}\), \(B_m=x^{.5+\Delta}\), \(z_q=x^{T^{-3}}\), and \(z_m=x^{T^{-23}}\). The original actual prime \(x^{.10}<s<x^{.14}\) obeys \(n=sq\in(x/2,x]\), \(m=N-n\), \((n,N)=1\). Use the literal \(W_s(q)\), \(M_N=\mathfrak S(N)x/(2L)\), \(J=\log(7/5)-.1408\) and \(T_q\) of the joint projection. Write \(\mathcal S_c\) for the physical sum with both \(q,m\) squarefree composite, \(P^-(q)>z_q,P^-(m)>z_m\), with central and unit support as above. The genuine prime–product source \(\mathcal S_p\) has prime \(q\), and squarefree composite \(m\) with \(P^-(m)>z_m\), retaining the same \(s,n,m\) support.

Let \(P\) be any fixed odd real polynomial with \(P(1)=1\) and \(P(t)=O(t^3)\) at zero. Define the literal strict-short score and the exact mathematical half score by
\[
 R_P(m)=\sum_{d\mid m,d<m/B_m}\mu(d)P(1-2\log d/\log m),\qquad
 R_P^*(m)=\sum_{d\mid m,d<\sqrt m}\mu(d)P(1-2\log d/\log m).
\]
Then uniformly at the actual target,
\[
 Z_N= 2P'(1)J M_N+\mathcal S_c\big[W_s(q)(\log m)T_q(q)R_P^*(m)\big]+o(M_N).
                                                                    \tag{1}
\]
The strict sufficient eventual threshold for the composite sum in (1) is
\[
 \big((1-2P'(1))J+.010\big)M_N
\]
with a fixed strict margin. This is not the threshold of an earlier composite representation.

For odd squarefree \(k=\Omega(m)\), write \(m=\prod_{i=1}^k p_i\), \(a_i=\log p_i/\log m\). Full complementary reflection gives
\[
 R_P^*(m)= H_{P,k}(a):=\frac12\sum_{I\subseteq[k]}(-1)^{|I|}
                           P\Big(1-2\sum_{i\in I}a_i\Big).          \tag{2}
\]
Consequently every odd rank greater than \(\deg P\) is identically zero. All the remaining odd composite terms in (1), with \(3\le k\le\deg P\), have the exact fixed-target transfer
\[
 \mathcal S_c[W_s(\log m)T_q,H_{P,k}1_{\Omega(m)=k}]
   =-\mathcal S_p[W_s(\log m)H_{P,k}1_{\Omega(m)=k}]
     +O_A(x L^{-A})                                                   \tag{3}
\]
for each fixed \(A>0\).

In particular, take \(P(t)=t^3\). The sole remaining odd rank is then \(3\), with \(H_{P,3}=24 a_1a_2a_3>0\). On a genuine high reflected prime \(r>B_m\), the score \(R_P(m)\) is over *all* divisors of its cofactor, and is zero if that squarefree cofactor has rank greater than 3. For rank two of \(m\) it is \(1-(1-2a)^3\ge0\), where \(a=\log(m/r)/\log m<1/2\). For rank four it is \(48 a_1a_2a_3\ge0\), where the three cofactor exponents are normalized by \(\log m\). Rank three is already included in (3). The high reflected rank-two and rank-four terms also transfer as in (3), imposing the same genuine high-prime condition on both sides. Thus for this particular \(P\),
\[
 Z_N=6J M_N-H_N+
  \mathcal S_c[W_s(\log m)T_q R_P^*,1_{\Omega(m)\ge4\text{ even},\,P^+(m)\le B_m}]
     +o(M_N),                                                       \tag{4}
\]
where \(H_N\ge0\) is the literal sum of the two high-rank favorable transfers just described and the **whole** reflected rank-three transfer (so rank-three high is counted once). This formula neither lower bounds \(H_N\) nor caps the remaining smooth even term at the new threshold.

## 2. Arithmetic proof of projection

First use \(R_P\) instead of \(R_P^*\). Its prime atom is 1. Replace both exact rough guards by the same Bonferroni polynomials as in the joint projection. Fixed divisor weights suffice since \(P\) is bounded on \([-1,1]\), and the same restoring factorial bound holds. The all-integer opened CRT term is zero to arbitrary log reserve by the original short \(q\)-side masked \(\mu/d\) harmonic. Indeed the unchanged literal \(s d_q\) range is \(\le x^{.499}\), the additional label exponent is \(T^{-1}\) on that side, and the reflected modulus exponent is \(\le .5-\Delta+T^{-21}\). The exact unit restrictions and movement of \(n\) are as before. Genuine prime \(m\) contributes zero by the same ordinary maximal prime BV at \(s\operatorname{lcm}(d_q,e_q)\) with the true cutoff and masked \(\mu/\phi\) harmonic. The both-prime atom equals \(Z_N\) up to proper prime powers, whose weight is \(x^{1/2+o(1)}\) since the opposite product has at most a fixed-divisor-power multiplicity.

For genuine prime \(q\), the source is the physical prime product \(n=sq\), with both slots polynomially long. Apply the same maximal-prefix genuine-product BV of the joint projection at the reflected modulus \(D=\operatorname{lcm}(d,e)\le1.5x^{.5-\Delta+T^{-21}}\). This is below \(x^{1/2}/L^B\) for every fixed \(B\). The prime masks, divisor-weighted discrepancy, log-relative meshes, and exact reflected prefix \(n<N-B_m d\) are unchanged. Undo the meshes and fix actual \(s,q,m\) in the coprime principal. Write \(d=a k\), \(a\mid e\), \((k,e)=1\); the term is zero unless \((e,Nn)=1\). The remaining harmonic is
\[
 \sum_e\frac{\mu(e)}{\phi(e)}
 \sum_{a\mid e}\mu(a)
 \sum_{k<m/(B_ma),\ (k,eNn)=1}\frac{\mu(k)}{\phi(k)}
     P\left(1-2\frac{\log a+\log k}{\log m}\right).                \tag{5}
\]
Here \(e\) is the genuine finite Bonferroni label, with \(e\le x^{T^{-21}}\), and all retained upper endpoints are polynomially long.

For even polynomial-sized mask \(V=eNn\), the finite harmonic log moments of fixed order \(j\) equal their Abel limits up to arbitrary log reserve uniformly over such endpoints. This follows by partial summation and integrating the uniform finite tail estimate for \(\mu(k)/\phi(k)\) in [Huang--Li, arXiv:2005.03811v2, Lemma 1](https://arxiv.org/pdf/2005.03811v2), quoting Goldston--Yıldırım, as used in the joint projection (the endpoint can increase without weakening the mask condition). The Abel limits are \((-1)^j F_V^{(j)}(0)\) for \(F_V(z)=\sum_{(k,V)=1}\mu(k)/(\phi(k)k^z)\). Factoring \(F_V(z)=\zeta(1+z)^{-1}E_V(z)\) gives moment 0 for \(j=0\), \(-\mathfrak S(V)\) for \(j=1\), and \(O_j(\mathfrak S(V)T^{O_j(1)})\) for every fixed \(j\). Here \(E_V(0)=\mathfrak S(V)\); for the derivative bound split the finite factors at \(p=L^2\) and use \(\sum_{p\mid V,p>L^2}(\log p)^j/p=O_j(T^j)\), e.g. the large-p summand per \(\log p\) is maximized at \(L^2\) and \(\log V=O(L)\). The infinite residual Euler factors have bounded derivatives because their deviation from 1 is \(O(p^{-2+o(1)})\).

In (5) expand the fixed polynomial into monomials in \(\log k,\log a\). For \(j\ge1\) fixed, the contribution of \((\log a)^b\) paired with the \(\log k\) moment of order \(j\) vanishes after the \(a\)-sum when \(\omega(e)>b\); for \(b\ge\omega(e)\) the \(a\)-sum in absolute value is at most \(C_P(1+\log e)^{b-\omega(e)}\prod_{p\mid e}\log p\), by the elementary finite-difference formula. Thus \(e\ne1\) uses at most \(\deg P-1\) primes, and
\[
 \sum_{p\le z_m}\frac{\log p}{L(p-1)}\ll T^{-23}.
\]
The singular factor \(\mathfrak S(eNn)/\mathfrak S(N)\) is bounded pointwise for nonvanishing main terms, since \(n\) has two macro primes and \(e\) has at most \(\deg P-1\) primes, all odd. It follows that all \(e\ne1\) terms of (5), and all log moments of order at least two, total \(o(\mathfrak S(N)/L)\) uniformly. For the two moment estimates here one uses the sharper exact \(j=1\) formula with *no* factor \(T^{O_P(1)}\), and the extra factor \(L^{-1}\) for \(j\ge2\). All finite-truncation errors have arbitrary log reserve by summing the original absolute harmonics and the extra fixed log powers before cancellation. The surviving term \(e=1,j=1\) is \(2P'(1)\mathfrak S(Nn)/\log m\). The ratio \(\mathfrak S(Nn)/\mathfrak S(N)=1+o(1)\) is uniform since \(n=sq\) has two actual macro primes. Summing with the original weights and \(\log m\), and using ordinary PNT for \(s,q\), gives the stated \(2P'(1)J M_N\). Inclusion–exclusion proves (1) with \(R_P\) in place of \(R_P^*\). Squareful rough rows can be removed using the same Cauchy and proper-square support estimates as before.

For the exact half replacement note \(B_m>\sqrt m\) eventually over the entire physical window. The difference uses only true divisors \(x/B_m\le d\le\sqrt{1.5x}\) and weight \(O_P(\Delta^3)\) per divisor. At fixed \(s,d\), write \(m=d v\) and use the same primitive affine forms \(q,v\) as in the joint projection, of free length \(\asymp x/(s d)\), determinant \(N\), and with true unit masks. Majorize by \(2^{\omega(q)}1_{P^-(q)>z_q}\) and \(1_{P^-(v)>z_m}\) in corrected Henriot. The extra local ratio over the primes of \(d\) is \(1+o(1)\) since \(\omega(d)\le T^{23}\) and every prime is \(>z_m\); the slope prime \(s\) also costs \(1+o(1)\). The envelope is \(\ll \mathfrak S(N)(x/(s d))L^{-2}T^{6+23}\). A dyadic one-dimensional rough upper gives
\[
 \sum_{x/B_m\le d\le\sqrt{1.5x},\ P^-(d)>z_m}\frac1d
       \ll \frac{1+\Delta L}{\log z_m}\ll T^3
\]
using \(O(1+\Delta L)\) dyadic intervals of comparable polynomial length. The log weight \(\log m\) and bounded \(s\)-harmonic now give total \(O_P(M_N T^{-28})\). This covers all ranks at once, with no unwarranted uniform bound on their divisor counts. A mathematical equality divisor at \(\sqrt m\) would have polynomial weight zero anyway.

## 3. Rank-specific product transfer

For odd squarefree \(k\), complementing subsets changes their Möbius sign by \(-1\); the polynomial argument also changes sign, proving (2). The full signed finite difference of order \(k\) vanishes if \(k>\deg P\). For the several remaining fixed ranks, \(H_{P,k}\) is a finite sum of separated monomials in actual prime logs divided by fixed powers of \(\log m\). The special high even ranks for cubic use the analogous polynomial cofactor weights, with the genuine high condition, and may be treated separately. To see (3), first allow **all** \(q\) in this physical source and show the whole \(T_q\)-sum is log-small.

In an odd rank \(k\) profile, label a genuine prime \(r\ge x^{1/(2k)}\) of \(m\) and write \(m=r v\), with the other \(k-1\) actual prime factors in \(v\). Normalize each choice by the reciprocal of the number of qualifying primes, namely \((1+\#\{p\mid v:p\ge x^{1/(2k)}\})^{-1}\), which depends on \(v\) only. At least one giant enough prime exists, and the exact polynomial weights separate by symmetry. This avoids imposing a prime-vs-prime order cutoff on the SW axis. The temporarily recombined case \(r\mid v\) lies on true square support with \(r^2\mid m\) and contributes at most \(x^{1-c_k+o(1)}\) (sum multiples of \(r^2\) over \(r\ge x^{1/(2k)}\), then fixed divisor multiplicity and weights); it need not be declared impossible in the input theorem. In the special even high ranks simply label their unique genuine \(r>B_m\), with no ordering constraint. Restrict the independent cofactor coefficient to its exact \(z_m\)-rough squarefree product and retain actual target masks on both slots.

If \(v\ge x^{.0005}\), use generalized product BV at scale \(x\), with actual prime \(r\) as SW slot, as in HighReflectedCompensationByComplement. Keep \(q\)-modulus \(s\operatorname{lcm}(d_q,e_q)\le x^{.499+1/T}<x^{.4995}\), where \(e_q\) is the original Bonferroni guard. If \(v<x^{.0005}\), fix \(v\) and use ordinary maximal prime BV at scale \(x/v\ge x^{.9995}\), with real reduced residue \(N\bar v\) modulo that same modulus only when \(v\) is coprime to it. Harmonic summation \(\sum_{v\le x}\tau(v)^C/v\) absorbs the fixed cofactor coefficient and all log weights. In both branches keep the literal moving prefix \(m<N-s B_q d_q\), and use the same weighted discrepancy reserve, smooth weight separation, independent unit masks and log meshes. No theorem for one short arbitrary slot is needed.

After restoring the coprime principal, the remaining \(T_q\) opening at fixed actual \(s,m,e_q\) splits \(d_q=a k\), \(a\mid e_q\), and yields exactly the same uniformly tiny masked \(\mu(k)/\phi(k)\) harmonic as the high-reflected null. Its actual cutoff \(q/(B_q a)\) is polynomially long. The small \(s^{-1}\) correction if \(s\mid k\) is paid by the harmonic reserve. Thus the all-\(q\) term is \(O_A(x L^{-A})\). Genuine prime \(q\) has \(T_q=1\), proving (3). Its orthogonal squareful \(q\) portion is log-small by prior rough square-support Cauchy. For (4), replace \(R_P^*\) by \(R_P\) only in the high family upon the absolute collar bound. With cubic polynomial the complete cofactor moments above apply and no high rank beyond 4 remains. Its low reflected rank-two collar is \(o(M_N)\), as in the joint projection (for bounded \(R_P\) at rank two). The new favorable sum is not credited again against overlaps from earlier ledgers.

## 4. Exact angular calibration constraint

For \(k\ge2\), use the literal unordered prime-product angular weight \(da/(k!\prod_i a_i)\) on \(a_i>0,\sum_i a_i=1\), where \(da\) is Lebesgue in the first \(k-1\) coordinates. For \(k=1\) use a unit atom at \(a_1=1\). Then the total \(H_{P,k}\) angular coefficient over the odd composite ranks is
\[
                 \sum_{k\ge3,\ k\ \mathrm{odd}}\int H_{P,k}\,\frac{da}{k!\prod a_i}
                         =P'(1)-1.                                 \tag{6}
\]
To prove this, it suffices to use \(P(t)=t^D\) for odd \(D\). The exponential generating kernel for the whole signed difference at \(\sum a_i=1\) is \(\prod_i 2\sinh(z a_i)\). Temporarily permit \(\sum a_i=t\ge0\) and take the one-dimensional Laplace transform in \(t\). The ordered convolution integrates to \(\left(\log((w+z)/(w-z))\right)^k\) for real \(w>|z|\). Summing odd \(k\) with factor \(1/(2k!)\), one gets
\[
 \frac12\sinh\left(\log\frac{w+z}{w-z}\right)=\frac{w z}{w^2-z^2},
]
whose inverse is \(z\cosh(z t)\). At \(t=1\) the coefficient of \(z^D/D!\) is \(D\). Coefficientwise, each fixed \(D\) has only finitely many ranks and the rank-one atom is exactly 1, proving (6).

There is also an absolutely convergent exact angular identity for the **even** ranks, with the full half score \(R_{P}^{*}\) evaluated on the simplex:
\[
                 \sum_{k\ge2,\ k\ \mathrm{even}}\int R_{P}^{*}(a)\,\frac{da}{k!\prod a_i}
                       =P'(1).                                      \tag{7}
\]
For even rank the half sum equals one half of the complete signed difference of \(\Phi(s)=P(|s|)\) on \([-1,1]\). Extend \(\Phi\) to an even compactly supported function with a smooth cutoff equal to 1 in a neighborhood of that interval. Since \(P\) vanishes to order at least 3 at zero, the Fourier transform (in the inversion convention \(\Phi(s)=\int \widehat\Phi(u)e^{ius}du\)) is \(O_P((1+|u|)^{-4})\), by integrating by parts on the two halves. The signed difference of this Fourier character is \(\prod_i 2i\sin(u a_i)\). At fixed \(u\), the absolute simplex integral of the product divided by \(\prod a_i\) is at most
\[
 2 k\left(\int_0^1\frac{2|\sin(u a)|}{a}\,da\right)^{k-1};
]
indeed insert \(\sum_i a_i=1\), bound the corresponding numerator by 2 and integrate the other coordinates over their full cube. After dividing by \(k!\) and summing, this is \(O((1+|u|)^2)\), sufficient for absolute Fourier Fubini. In the total scale \(t\), Laplace transform of the summed even convolutions, without the overall half, is
\[
 \cos(2\arctan(u/w))-1=-\frac{2u^2}{w^2+u^2}.
]
Its inverse is \(-2u\sin(u t)\); termwise transforms are justified either by the absolute exponential majorant for sufficiently large real \(w\), or directly by the same convolution argument up to arbitrary bounded \(t\). The continuous inverse at \(t=1\) with the half factor now integrates to \(-\int u\sin u\,\widehat\Phi(u)du=\Phi'(1)=P'(1)\). This proves (7); it is an angular identity, **not** a fixed-target theorem uniformly in unbounded even prime rank.

For the finitely many odd nonzero ranks, the angular identities also constrain a true positive-part strategy. On any fixed compact angular region, count genuine \(q\prime\) and the true reflected prime factors over even \(N\in[2Y,4Y]\), using ordinary PNT for the terminal primes after fixing the actual small factor slots. As in BooleanComplementaryBand, the physical domain in \(n,m\) has area \(3Y^2/2\), the mean singular normalizer is \((3Y^2/2)/\log Y\), and the \(s\)-integral gives \(J\). Avoid the finitely many equal-exponent cross-leg surfaces and approximate them by strips of arbitrarily small measure in the compact profile. This ensures disjoint prime labels and the true unit condition without assuming targetwise independence. For fixed rank the angular integrability on approaching the boundary follows from the finite-difference bound \(|H_{P,k}|\ll_P\prod a_i\). Apply the result to \([-H_{P,k}]_+\), or only to compact lower approximations, and let the compact regions fill the simplex. The resulting dyadic lower limit for the sum of the **positive parts of the prime-count terms after (3)**, normalized by the sum of \(M_N\), is at least
\[
                         J\,(1-P'(1))                              \tag{8}
\]
when \(P'(1)<1\), by (6). Thus lowering the explicit term of (1) to \(\le J M_N\) in this family forces a substantial adverse odd-rank positive part. In particular at exact calibration \(P'(1)=1/2\) the forced dyadic size is at least \(J/2>.097 M_N\), above the \(.010 M_N\) residual allowance of (1). This does not give its true signed sum, nor rule out using compensating even ranks or a different detector.

For a concrete exactly calibrated example take \(P(t)=\tfrac94 t^3-\tfrac54 t^5\). The sole possibly nonzero odd composite ranks are 3 and 5. The smooth rank-three sign is favorable: (2) equals \(4a_1a_2a_3(27/2-25\sum_i a_i^2)\), positive when each \(a_i\le1/2\). But rank five gives an everywhere adverse true prime-count term; its angular positive part is \(5/6\), since the monomial \(t^5\) contributes \(2/3\) at rank five. Thus this example has at least \((5/6)J M_N\) adverse positive part in weighted dyadic mean. It is not an improvement of the signed bound.
