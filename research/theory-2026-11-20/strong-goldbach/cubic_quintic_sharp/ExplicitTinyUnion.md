# A numerical tiny-factor cutoff for the cubic–quintic detector

Use the genuine fixed even target, actual central intervals \(NJ,N(1-J)\),
target units, \(L=\log N\), \(M=|J|N\mathfrak S(N)\), and the sharp
\(F,H,\Pi,R_J\) of [the cubic–quintic detector](CubicQuinticSharp.md).
Here \(J\Subset(1/3,2/3)\) is fixed and nondegenerate. Put
\[
 b=1/5000,\qquad I=1_{\{P^-\le N^b\}},\qquad T=IH.
\]

**Theorem.** The contribution of the whole actual union where either
coordinate has a prime factor at most \(N^{1/5000}\) is greater than
\(-.456M+o(M)\). Thus, with original sharp scores everywhere,
\[
 R_J\ge .059M+\sum_{\substack{x+y=N,\ x\in NJ,\ (x,N)=1\\
        \min(P^-(x),P^-(y))\in (N^{1/5000},N^{.150}]}}
                  H(x)H(y)+o(M).
\]
This uses the disjoint whole bilateral \(.150\)-rough block \(>.515M\)
of the detector proof. It asserts neither a lower on the remaining
signed sum nor a bound at \(b=.003\).

## 1. Literal product stop and exact signed comparisons

Put \(\kappa=9/2\), \(c=\kappa b\), \(d=c+10^{-8}\), \(w=20b\).
Let \(B(v)=10v^3-15v^4+6v^5\) on \([0,1]\), extended by \(0\) to the
left and \(1\) to the right. Define
\[
 F_*(t)=F(t)B((1/2-t-d)/w),\quad H_*=\text{its true score},\quad
 E=H-H_*,\quad D=(1-I)E.
\]
The real \(F_*\) and \(F\) have identical jets at zero. Both are \(C^2\)
with third derivative of bounded variation after a suitable compact
left extension.

Fix \(0<a<b\). Let \(C\) be \(H_*\) times the nonempty inclusion–exclusion
sum for the actual bank \((N^a,N^b]\) stopped at actual subset-product
angle at most \(c\). In this paragraph and later, product angles for the
stop are \(\log h/L\). On a bank-hit row let \(p_0\) be its actual least
bank prime, \(u_0=\log p_0/L\); pairing each subset of the other marks
with its union with \(p_0\) shows that the difference between the bank
hit and the stop is exactly
\[
 \sum_{\substack{A\subseteq\text{actual other bank labels}\\
                  c-u_0<\sum_{p\in A}\log p/L\le c}}(-1)^{|A|}.
 \tag{1}
\]
Call \((p_0,A)\) a certificate and \(V\) the score \(H_*\) times (1).
There are at least five names in any certificate, since the joined
product \(h=p_0\prod_{p\in A}p\) has angle strictly \(>c>4b\) and
\(\le c+b\). There is no certificate on a prime.

We use the actual compact rank and positive-floor limits of
[TinyUnion, §1](TinyUnion.md) and
[ExplicitTinyStop, §1](../sextic_true_tag_rebate/ExplicitTinyStop.md).
For this score all relevant bounds tolerate \(1+2^{\omega(n)}\)
on each arm: multiply the prime phases by a fixed \(\nu>2\) so
close to \(2\) that \(\nu(4/\pi+\epsilon)<3\), leaving room for a
small marked-phase frequency power. Four integrations by parts give
\(\widehat F,\widehat F_*=O((1+|\xi|)^{-4})\), also after true own-log
dilation, so the genuine two-form and ordinary phase upper bounds
remain integrable. In particular this pays the rank tails and the
absolute removal of a factor \(p\le N^a\): extract its phase once
in the primitive forms \(v,N-pv\), and sum it with reciprocal \(1/p\)
using the marked phase bound from TinyUnion. First fix \(a\), take
large \(N\) and complete the compact limits; then let \(a\downarrow0\).
Thus one may restrict to global least prime \(p_0\) on certificate rows,
and (1) with \(T=C+E+V-D\) holds in the limiting normalized pairings.
\(C,V\) may depend on \(a\); every ordinary or paired identity concerning
them below denotes this specified limit. On fixed compact floors, true
own-log to target-log changes are \(o(M)\): the local score is Lipschitz in
the finitely many angles, and genuine polynomial rough pair counts are
\(O(M/L^2)\). The same argument works with a true prime arm, and
squareful rows on compact floors have the usual power-saving bound.

Here \(m(Z)\) is genuine unopposed angular mass, from the actual
fixed-rank product PNT, so \(\sum_{n\in NJ,(n,N)=1}Z(n)\) is
\(|J|N m(Z)+o(N)\) on compact sources, and the normalized limit
defines \(m\) for the above scores. Use the real short transfer
of [TinyUnion, §2](TinyUnion.md) on the actual subset \(h\):
its free profile is \(\prod_{p\mid h}(1-\mathcal T_{\log p/L})F_*\).
At fixed \(a\), discard the actual joined-prime squares and retain the
squarefree label \(e\le N^{\min(a,d-c)/4}\) by the literal square
bounds. Its grouped tested modulus satisfies
\[
 [h\ell,e^2]\le N^{1/2-(d-c)/2}.
\]
There are divisor-power multiplicities at each grouped modulus,
and the genuine opposite arm is a compact-sourced product for
ordinary product BV at this strict level; rank one uses true prime
BV. In the short principal retain the \(Nh\) and actual source unit
mask and \((\ell,h)=1\). The local completion is the same as the
cited transfer, with \(h/\varphi(h)=1+o_a(1)\); no prime of a fixed
compact source has a nonnegligible extra reciprocal effect.
All positive subset labels are actual, and every order \(j\le4\)
is uncut because \(jb<c\). On all allowed marks the derivative
is the original polynomial \(F'\) of degree four, since
\(c<1/2-d-w\). Every finite difference of order \(j\ge5\) is zero.
Consequently, in either orientation, for each such genuine \(Z\),
\[
 \langle C,Z\rangle=m_b\,m(Z)M+o(M),\qquad
 m(C)=m_b=-32b+288b^2-\tfrac{2720}{3}b^3+\tfrac{3040}{3}b^4.
 \tag{2}
\]
For the ordinary version use the same one-form signed harmonic, or
the completed marked derivatives against the true product PNT.
The coefficient is the four-term expression from TinyUnion, with
the artificial \(a\) floor removed. Fixed \(a\) supplies a bounded
number of marks independently of their order, so this is a finite
computation before taking any limit. The square-root-level margin
is fixed and strict.

The short transfer for a raw arm on genuine compact product
sources is \(2m(Z)M\), from \(F'(0)=-2\). For the sharp raw arm, taper
at half and then take the genuine Fourier comparison from the original
cubic–quintic proof. The defect \(E\) has zero jets, so \(m(E)=0\)
and both pairings of \(E\) with \(Z\) are \(o(M)\); for a genuine
prime \(Z=\Pi\) use true prime BV. For \(H=V_{\rm raw}-\Pi\) the
prime term is kept literally. All these statements apply to
\(C,V,D\) and their linear combinations by the physical rank/floor
limits above. In particular \(m(H)=1\), and no statement here
replaces \(\langle\Pi,\Pi\rangle\).

We also need the actual ordinary \(m_T=m(T)\), to accuracy
\[
 |m_T-m_b|<10^{-12}.                                             \tag{3}
\]
Indeed on the ordinary genuine \(b\)-rough arm the divisor angular
formula for the raw score is
\[
 \int_{[0,1/2]}F(t)\,d(1_{t\ge0}\rho(t/b))\,\omega((1-t)/b)/b,
\]
where \(\rho,\omega\) are the Dickman and Buchstab functions. This is
the ordinary factorial convolution of real prime factors, as in
[ExplicitTinyStop, §2](../sextic_true_tag_rebate/ExplicitTinyStop.md):
one signed divisor convolution, one positive quotient convolution.
The full ordinary prime mass \(1\) is on the no-hit arm. On this
support replace \(\omega\) by \(e^{-\gamma}\): for \(k\ge3\) its
derivative supremum beyond \(k\) is at most \(1/k\) times the
previous one, by \(u\omega'(u)=\omega(u-1)-\omega(u)\) and the
mean value bound. Its initial derivative supremum beyond 2 is
\(\le1\). The resulting limit error is factorial at \(k=2500\).
Integration by parts gives minus the average of \(F'(bU)\)
under probability density \(e^{-\gamma}\rho(U)\,dU\);
extending the polynomial past half costs a factorial tail
since \(\rho(U)\le1/\lfloor U\rfloor!\).
For instance the two errors together are bounded by
\(3000(2502)^4/[b(2499)!]<10^{-12}\), using
\(|F'(t)|\le600(1+t^4)\) for its polynomial extension.
The four moments of \(U\) are those in TinyUnion, giving
\(2+\mathbb E F'(bU)=m_b\). This proves (3).

Write \(R_0=V-D\), so \(m(R_0)=m_T-m_b\). Equations (2) and the
genuine short transfer give
\[
 \begin{split}
  \langle T,H\rangle/M
     &=m_b+2m(R_0)-\langle R_0,\Pi\rangle/M+o(1),\\
  \langle T,T\rangle/M
     &=m_T^2-m(R_0)^2+\langle R_0,R_0\rangle/M+o(1).
 \end{split}                                                     \tag{4}
\]
The first equation holds in either orientation with the true prime cross
in that orientation. Since \(R_0\) is zero on primes, the
[genuine angular prime upper](../angular_prime_first_composite/Proof.md)
of \(3.446\) for nonnegative compact composite sources applies to its
positive part, followed by the physical limits. Thus its upper in (4)
is at most \(3.446\{m(|V|)+m(|D|)+10^{-12}\}/2\).
This accounts for the factor \(1/2\) from the actual near-zero
ordinary signed mass of \(R_0\), not a parity model of the reflection.

## 2. Actual absolute paired prices

Put \(e(s)=F(1/2-s)-F_*(1/2-s)\ge0\), supported on \([0,d+w]\).
For the \(b\)-rough defect the real sieve bounds of
[ExplicitTinyStop, §2](../sextic_true_tag_rebate/ExplicitTinyStop.md)
apply with this cubic zero:
\[
 m(|D|)\le B_D=b^{-2}\int e(s)\,ds,\qquad
 \langle Z,|D|\rangle/M\le U_D\,m(Z)+o(1),\quad
 U_D=(2/b)\int e(s)\,ds/s+(2/3)B_D.                              \tag{5}
\]
Here \(Z\) is any nonnegative genuine compact product source and the
bound also holds in reflection. For the ordinary estimate the divisor
and quotient rough densities are each \(\le1/b\). For the real
paired bound, open the true \(N^b\)-rough divisor of angle \(1/2-s\).
Its quotient is genuinely \(N^b\)-rough, so the actual quotient sieve
has level exponent tending to \(s\) within strict subroot product BV.
Use the true reduced local density on all unit rows. The linear upper
multiplier is \(2/s\) for \(s\le3b\) (if \(s\le2b\), sift to
\(s/2\)), and at most \(2/(3b)\) for \(s>3b\). First work away from
\(s=0\) and with strict level margins. To remove that collar, use a
smooth localization of the **signed defect score** near half, not an
unsigned bare divisor sum there: its weighted Fourier norm is
\(O(\eta^{3-\sigma})\) on width \(\eta\), with the physical phase
exponent \(\sigma<3\) from §1. The remaining compact limit justifies
(5), including with \(Z=|D|\) or \(|V|\).

Use the certificate estimates of
[ExplicitTinyStop, §3](../sextic_true_tag_rebate/ExplicitTinyStop.md)
with the present score and cutoff. For completeness let \(x_0=u_0/b\)
and use weight \(x_0^{3/2}\) on each genuine certificate. On each
actual integer put
\[
 X=(H_*/L)^2\sum_{\rm cert}x_0^{-3/2},\qquad
 Y=\sum_{\rm cert}x_0^{3/2}.
\]
Before summation, AM–GM on each actual ordered pair of certificates
bounds \(|V(x)V(y)|\) by
\(L^2(X(x)Y(y)+Y(x)X(y))/2\). For an actual compact nonnegative
source \(Z\), open the real certificate product \(h\)
and upper-sift the free quotient to its genuine least \(p_0\).
The tested level is \(N^{.499}/h\) and the ratio exceeds 3.
All \(h\) labels are at least \(p_0\), so the sieve label is
coprime to \(h\); target units retain precisely the usual reflected
singular factor. The resulting conditional multiplier is
\(2/(3u_0 h)\) including the reciprocal certificate label, with the conventional
normalizations by \(L\). For fixed \(x_0\) the ordinary harmonic
density of the other labels at total \(s\) is at most
\(\omega(s/x_0)/x_0\), dropping their upper ceiling. On the
width-\(x_0\) window of (1), \(s/x_0\ge3.5\), so
\(\omega(s/x_0)\le.6\); use the elementary formula on \([2,3]\)
and the recurrence onward. Integrating \(x_0^{-1/2}\) over
\([0,1]\) gives \(\langle Z,LY\rangle/M\le(.8/b)m(Z)+o(1)\).
Apply it to the actual compact \(Z=LX\) before removing the
truncations. This proves
\[
 \langle |V|,|V|\rangle/M\le(.8/b)B_X^2+o(1)
 \quad\text{if }\quad \sqrt{m(LX)}\le B_X.                        \tag{6}
\]
All conditional bounds here are true product BV and upper sieves on
actual quotients of \(N-x\), not an independent probability model.

## 3. Effective ordinary bounds and the certificate

Write \(J_j(v)=\int_0^v |1-e^{it}|^jdt/t\), \(j=1,2\), and let
\(C_j(\tau)\) be the genuine ordinary certificate harmonic, with each
named angle \(x\) scaled by \(b\) and phase factor
\(|1-e^{i\tau x}|^j\). For \(j=2\) include also \(x_0^{-3/2}\).
The other named factors are unordered. Put \(v_0=1-c-b\).
The actual ordinary factorial convolution of the remaining factors
has positive phase-weighted density at total \(v\ge v_0\)
at most \(2^j e^{J_j(|\xi|)}/v_0\): multiply the convolution
by its total length, select one factor, and use
\(|1-e^{i\xi t}|^j\le 2^j\). Fourier inversion and Minkowski
on the same ordinary integer and its certificate give
\[
 \begin{split}
 m(|V|)&\le B_V=\frac{2}{\pi v_0}\int_0^\infty
 |\widehat F_*(\xi)|e^{J_1(\xi)} C_1(b\xi)\,d\xi,\\
 \sqrt{m(LX)}&\le B_X=\frac{2}{\pi\sqrt{v_0}}\int_0^\infty
 |\widehat F_*(\xi)|e^{J_2(\xi)/2}\sqrt{C_2(b\xi)}\,d\xi .
 \end{split}                                                     \tag{7}
\]
No physical independence assumption occurs in these ordinary
integrals. At \(\tau\le1\) there are at least four other marks.
Their individual harmonic masses are bounded by
\(\tau(1-x_0)\) or \(\tau^2(1-x_0^2)/2\).
The exponential tails from order four, integrated with the
least mark, give \(C_1(\tau)\le e^\tau\tau^5/120\) and
\(\sqrt{C_2(\tau)}\le \sqrt{e^{1/2}/192}\,\tau^5<.1\tau^5\).
At \(\tau\ge1\) use the same positive convolution recurrence on
the other labels at total \(s\ge\kappa-1\), the exact window width
\(x_0\), and \(\int_0^1\min(2,\tau x)^2x^{-3/2}dx\le8\sqrt\tau\).
This gives
\[
 C_1(\tau)\le4e^{J_1(\tau)}/(\kappa-1),\qquad
 C_2(\tau)\le32e^{J_2(\tau)}\sqrt\tau/(\kappa-1).
\]

For the Fourier transform use the common left extension: if
\(e_*=3/5\) and \(u=-t/e_*\), on \(0\le u\le1\) multiply
\((1-u)^4\) by the degree-three Taylor polynomial of
\(F(-e_*u)/(1-u)^4\) (the polynomial branch at zero), and set
the profile to zero farther left. It matches the third jet at zero.
Let \(C_0=1.203\), \(C_4=7316.488\). The attached checker
bounds \(\|F_*\|_1<C_0\) and the variation of its third
derivative by \(C_4\), hence
\(|\widehat F_*|\le\min(C_0,C_4|\xi|^{-4})\).
Use midpoint rational integration plus the Bernstein derivative
supremum to bound each polynomial \(L^1\) norm. In the variation
include the two jumps of the third derivative, with exact magnitudes
\(60F(1/2-d)/w^3\) and \(60F(1/2-d-w)/w^3\).
There is no other jump. The base fourth derivative integral is \(\le480\).

Put \(A=23/5,\ \nu=51/40,\ K=9/4\). The checker certifies the
elementary bounds \(e^{J_1(v)}\le A\max(1,v^\nu)\) and
\(e^{J_2(v)/2}\le K\max(1,v)\), also \(e^{J_2(v)/2}\le2v\)
at \(v\ge20\). For the first use the alternating sine Taylor over
the first period; the primitive of \(|1-e^{it}|-4/\pi\)
there has absolute size less than \(1\), by its convex first
half and symmetry and a checked Taylor lower on that half.
The excess after the first period is at most \(1/(2\pi)\)
by integration by parts. For the second apply the alternating
cosine Taylor for \(v\le20\); beyond it use
\(J_2(v)/2=\gamma+\log v-\operatorname{Ci}(v)\) and
\(|\operatorname{Ci}(v)|\le2/v\).
The rational endpoint grids and logarithm enclosures are in the checker.

Splitting (7) at \(\xi=1,1/b\) yields the following two actual
upper numbers for the names \(B_V,B_X\) in (5)–(7):
\[
 \begin{split}
 B_V&\le \frac{2}{\pi v_0}\left[
 C_0b^5/80+C_4 b^{69/40}
 \left(\frac{A}{40(\nu+2)}+\frac{4A^2}{(\kappa-1)(3-2\nu)}\right)\right],\\
 B_X&\le \frac{2}{\pi\sqrt{v_0}}\left[
 C_0Kb^5/60+C_4 b^2\left(K/30+\tfrac83 K\sqrt{32/(\kappa-1)}\right)\right].
 \end{split}
\]
The true union is \(\langle T,H\rangle+\langle H,T\rangle
-\langle T,T\rangle\). By (3)–(7) its absolute debit is at most
\[
 -2m_b+m_b^2+3.446(B_D+B_V)+(B_D+2B_V)U_D
       +(.8/b)B_X^2+10^{-8}<.456 .
\]
The \(10^{-8}\) covers both signed ordinary errors in (3)–(4).
The replay prints the upper arithmetic value \(.45557051\);
every enclosure used to check the strict threshold is rational.

Run:

    python3 -OB check_explicit_cq_tiny.py
