# A degree-six half-zero detector with a true small-factor prime rebate

Let \(N\) be an individual large even integer, \(L=\log N\), and
\(J\Subset(1/3,2/3)\) a fixed nondegenerate interval. In
\(\langle X,Y\rangle=\sum_{x\in NJ,(x,N)=1}X(x)Y(N-x)\), put
\(M=|J|N\mathfrak S(N)\), \(\Pi(n)=1_{n\ {\rm prime}}\log n\), and
\(R_J=\langle\Pi,\Pi\rangle\). Use this **different** half-zero profile:
\[
 \begin{split}
 F(t)&=44(1/2-t)_+^4-112(1/2-t)_+^6\qquad(t\ge0),\\
 H(n)&=1_{n\ {\rm squarefree}}\left[
  (\log n)\sum_{d\mid n}\mu(d)F(\log d/\log n)-\Pi(n)\right].
 \end{split}                                                     \tag{1}
\]
In particular \(F(0)=1,F'(0)=-1\). Let \(B\) be the actual prime band
\(N^{.01}<p\le N^{.02}\), put \(k(n)=\#\{p\in B:p\mid n\}\), and set
\[
 Q(n)=[-H(n)]_+1_{P^-(n)>N^{.1251}},\qquad
 W(n)=\tfrac13 k(n)[-H(n)]_+1_{1\le k(n)\le3}.
\]
The supports are disjoint on a single arm and \(0\le Q+W\le[-H]_+\).
Write \(H_1=H+Q,\ H_2=H+Q+W\).

**Theorem.** Uniformly through the even targets,
\[
\begin{split}
 \langle H,H\rangle&=R_J-M+o(M),\\
 R_J&\ge .712M+\langle H_1,H_1\rangle+o(M),\\
 \langle W,\Pi\rangle,\ \langle\Pi,W\rangle&>.165M,\\
 R_J&\ge .520M+\langle H_2,H_2\rangle
       -\{\langle W,W\rangle+\langle Q,W\rangle+\langle W,Q\rangle\}
       +o(M).                                                     \tag{2}
\end{split}
\]
The genuine prime crossing is on the degree-six score, including
arbitrary ranks, not a model. The three nonnegative overlaps in the
last line are **unestimated**. No binary conclusion is claimed and
no earlier quartic debit or rebate is counted here.

## 1. Calibration and physical limits

Apply [the quartic half-zero proof, §§1–4](../halfzero_detector/Proof.md)
with \(F\). A fixed smooth taper at width \(\delta\) below half keeps
\(F(0),F'(0)\); its weighted Fourier error is \(O_j(\delta^{4-j})\)
for \(j<4\), by scaling the fourth-order seam with uniformly bounded
variation of the fourth derivative of the rescaled profile.
The same short signed CRT and genuine prime-BV principals give
\(M,-M,-M\) in the nonbinary terms. Proper prime powers cost
\(N^{1/2+o(1)}\) with the actual fixed divisor multiplicities.

The positive Fourier envelopes there permit fixed powers of
\(\omega(n)\) (take \(D>1\) with a little additional slack), and the
ordinary one-arm version uses one root product \(O(1/L)\) and
one multiplicative Euler factor. For a fixed true tag \(p\in B\)
write \(n=pv\); apply the same argument on the primitive forms
\(v,N-pv\) at scale \(N/p\), with a single root at the leading
prime \(p\), since \(p\nmid N\). This gives extra \(O(1/p)\)
uniformly in the tag range, with bounded reciprocal total.
For an actual prime opponent use the rough-indicator
majorization of its logarithmic weight. The marked truncated
profiles below have uniform Fourier decay \(O((1+|\xi|)^{-3})\)
when their fixed compact parameter intervals are kept; this is
enough for some \(D>1\) and a small-factor grace exponent.
First restrict finite rank and positive floor, with the same
absolute tails on ordinary or paired scales, then remove
actual large prime squares and switch own logarithms to \(L\).
The switch costs \(O(1/L)\) in the bounded normalized profiles
on the retained rough rows. The selected tag itself has
\(p^2\mid n\) only on a power-small set, even after fixed
divisor weights. These are real physical restrictions; limits
take \(N\to\infty\) before improving fixed truncations.

For a genuine bounded-angle finite-rank prime-product source \(Z\)
with fixed positive floor use the
[same actual product transfer](../halfzero_detector/OneArmRoughDebit.md#3-genuine-signed-transfer-and-a-genuine-upper-of-the-overlap):
\[
  \langle Z,H\rangle=M_Z-\langle Z,\Pi\rangle+o(M),\qquad
  M_Z=\mathfrak S(N)\sum_{x\in NJ,(x,N)=1}Z(x).                       \tag{3}
\]
The reduced mask \(Nx\) and the first-log moment
\(-\mathfrak S(Nx)\) are retained, with
\(\mathfrak S(Nx)/\mathfrak S(N)=1+o(1)\) on these actual
source factors. Taper/seam and boundary limits above apply also
to (3), and extend it to \(W\) by finite-rank and positive-floor
restriction since \(W\le|H|\). The hard tag band admits Jordan
approximation on every fixed compact angle range. All these
claims apply in the reflected orientation as well.

## 2. The whole rough negative-arm comparison

For a squarefree composite put \(u_i=\log p_i/\log n\),
\(\sum u_i=1,\ q=\sum u_i^2\), and let \(Y_j\) be the sum of
the \(j\) independent centered uniforms of lengths \(u_i\), with
symmetric unimodal density \(b_j\). Write \(H_r=H(n)/\log n\)
at rank \(r\). Complementary subset sums give the even ranks
as half a full polynomial difference; the fourth and sixth
derivatives are \(1056-40320(t-1/2)^2\) and \(-80640\).
Thus
\[
 H_4=(528-1680q)\prod u_i,\quad H_6=-40320\prod u_i,\quad
 H_r=0\ (r\ge8,\ r\ {\rm even}).                                 \tag{4}
\]
The distributional odd derivatives give
\[
 H_5=\prod u_i\{1056b_5(0)-40320\mathbb E|Y_5|\},\qquad
 H_7=\prod u_i\{1056 b_7''(0)-80640b_7(0)\}.                       \tag{5}
\]
Indeed the fifth derivative uses a mass at half and a
truncated first power, and the seventh uses a mass and its
second derivative; multiplying by \((-1)^r\prod u_i\)
integrates the derivative against the continuous relevant
density. Differentiating the largest two interval factors
shows \(b_7''(0)\le0\) and
\(|b_7''(0)|\le2/(u_{(5)}u_{(6)}u_{(7)})\), by subtracting
two values of the remaining symmetric unimodal density whose
height is at most \(1/u_{(5)}\). Parentheses denote ordering.

Rank five is nonpositive on the whole simplex. By
[Ball's cube slicing theorem](https://doi.org/10.1090/S0002-9939-1986-0840631-0),
the projection of the centered unit-side cube gives
\(b_5(0)\le\sqrt2/\sqrt q\). The survival function \(S(t)\)
of \(|Y_5|\) is log-concave, since the convolution density
is log-concave and its positive-side tail preserves this.
Hence \(S(s+t)\le S(s)S(t)\), and integration gives
\(\mathbb E|Y_5|\ge\sqrt{q/24}\). With \(q\ge1/5\) these
bounds give the sign in (5).
In the other direction the centered uniform interval of
density \(b_5(0)\) minimizes the variance among densities of
that height, so \(b_5(0)\ge1/\sqrt q\). Also a symmetric
unimodal density is a mixture of centered uniforms; Cauchy
on their lengths gives \(\mathbb E|Y_5|\le\sqrt q/4\).
Consequently
\[
           [-H_5]_+\le (10080\sqrt q-1056/\sqrt q)\prod u_i.      \tag{6}
\]

Put \(a_0=.1251\). Rank two has positive score since \(F\)
decreases. For rank three with no giant, set \(z_i=1-2u_i\);
they sum to one, and \(z_i^4(11-7z_i^2)/4\le z_i\) for
\(u_i\ge a_0\). With a giant, the score on the two smaller
angles is \(1-F(u)-F(v)+F(u+v)\), minimized at \(u=v=a_0\)
by convexity on \([a_0,1/2]\) and positive there. Thus all the
rough negative mass is \(Q=\sum_{j=4}^7 R_j\), where
\(R_j=Q1_{\omega=j}\); higher rough ranks are impossible.

The ordinary actual angular density at rank \(j\) is
\(du_1\cdots du_{j-1}/(j!\prod u_i)\), by actual prime
harmonics and PNT in the genuine last slot.
Put \(A_j=1-ja_0,\ \bar q_j=ja_0^2+2a_0A_j+2A_j^2/(j+1)\),
\(d=11/35-\bar q_4>0\). After the product of the \(u_i\)
cancels, \(\bar q_j\) is the ordinary simplex mean of \(q\);
at rank four its variance is \(2A_4^4/175\) by the Dirichlet
moments. The bound \((v-d)_+\le v^2/(4d)\), Jensen in (6),
and (4)–(5) give \(M_{R_j}\le(m_j+o(1))M\), with
\[
 \begin{split}
 m_4&=\frac{1680 A_4^3}{4!3!}\frac{2A_4^4/175}{4d},&
 m_5&=\frac{A_5^4}{5!4!}(10080\sqrt{\bar q_5}-1056/\sqrt{\bar q_5}),\\
 m_6&=\frac{40320 A_6^5}{6!5!},&
 m_7&=\frac{A_7^6}{7!6!}(2112/a_0^3+80640\cdot7).
 \end{split}
\]
The checker bounds \(R_j/L\) pointwise by \(b_j^*\) using
\(\prod u_i\le j^{-j},\ q\le(1-(j-1)a_0)^2+(j-1)a_0^2\).
For rank 5 keep also \(q\le u_{(5)}\) and
\(\prod u_i\le u_{(5)}((1-u_{(5)})/4)^4\), with outward
\(1/1000\) rectangles in \(u_{(5)}\). Rounded \(b_j^*\)
bounds are \(.807,1.024,.865,1.996\).

Use the [same actual rough receiver](../halfzero_detector/OneArmRoughDebit.md#3-genuine-signed-transfer-and-a-genuine-upper-of-the-overlap)
at \(\theta=.499\) on genuine source \(R_i\) and its reflection.
The reduced local factor is \(0\) on the primes dividing \(Nx\)
and \(1/(p-1)\) otherwise. Thus
\(\langle R_i,R_j\rangle\le
 A\min(m_i b_j^*,m_j b_i^*)M+o(M)\), where the standard
linear-sieve formula at \(3<\theta/a_0<4\) gives
\(A=2[1+(\theta/a_0-3)^2/4]/\theta<4.988\).
This uses genuine product BV followed by an integer rough
upper, not two independent prime distributions.
Expanding \(H_1=H+Q\), (3) and the positive overlaps
give the debit
\[
   2\sum m_i+A\sum_{i,j}\min(m_i b_j^*,m_j b_i^*)<.288.
                                                                    \tag{7}
\]
The prime rebates in these terms need not be used.

## 3. One true mark and the explicit prime-side seam price

Put \(a=.01,b=.02\). On \(n=pv\), \(p\) a designated actual
tag of angle \(t=\log p/L\), the exact profile after the
own-log limit is \(F(w)-F(w+t)\) on the divisors of \(v\).
There is no central prime atom on that arm. The tested
modulus is \(pd\), \(d\mid v,\ (d,p)=1\).
For \(j=4,6\), let \(g_j(z)\) be zero below zero, \(z^j\) on
\([0,1]\), and \(e^{-3(z-1)/4}[1+(j+3/4)(z-1)]\) above 1.
Set
\[
 \Phi_h(w)=44h^4g_4((1/2-w)/h)-112h^6g_6((1/2-w)/h).
\]
With \(h=t+\delta\) use
\(F(w)-\Phi_h(w)-F_\delta(w+t)\), where \(F_\delta\) is the
smooth taper in §1, zero above \(1/2-\delta\).
This restricts the actual modulus to \(pd\le N^{1/2-\delta}\).
Use genuine maximal prime BV, with the actual bounded-divisor
multiplicity of \(pd\) and uniform bounded weight variation
(or fine log mesh inside the strict margin).
The signed reduced \(\mu(d)/\varphi(d)\) model has the
actual mask \(Np\), first-log moment \(-\mathfrak S(Np)\)
and zeroth moment zero. The outer factor is \(1/\varphi(p)\)
and \(\mathfrak S(Np)/\mathfrak S(N)=1+o(1)\).
After \(\delta\downarrow0\) its principal is
\[
 M\int_a^b [F'(t)-F'(0)+\Phi_t'(0)]\,\frac{dt}{t}.                \tag{8}
\]
The exponential tail gives
\(\sup_{a\le t\le b}|\Phi_t'(0)|<10^{-7}\) by \((1/2)/t\ge25\).
The negative of the first two derivative terms has value
\[
 m_* =78(b-a)-288(b^2-a^2)+\tfrac{1504}{3}(b^3-a^3)
               -420(b^4-a^4)+\tfrac{672}{5}(b^5-a^5)
       =.6970467499\ldots .
\]
The shifted second-term taper costs \(o_{\delta\downarrow0}(M)\)
by the marked physical envelope. The genuine first-term error
\(\Phi_t\) needs the quantitative calculation below.

In the convention \(\widehat f(\xi)=\int f(t)e^{-i\xi t}dt\),
put \(a_\xi(s)=|1-e^{i\xi s}|\), \(g_\xi(s)=a_\xi(s)/s\)
for \(s>0\), and \(J(T)=\int_0^T|1-e^{iu}|du/u\).
The positive factorial angular convolution on the residual
total \(c\) has density \(B_\xi(c)=\sum_{\ell\ge1}
g_\xi^{*\ell}(c)/\ell!\). Marking one factor by its length
gives
\[
 c B_\xi(c)\le2e^{J(|\xi|c)},\qquad e^{J(T)}\le5\max(1,T^{4/3}).
                                                                    \tag{9}
\]
Indeed \(s g_\xi(s)\le2\). On the first period use the
sine Taylor upper \(T-T^3/72+T^5/9600\).
The periodic mean is \(4/\pi<4/3\); the centered primitive
\(4(1-\cos(u/2))-(4/\pi)u\) on that period has norm below 1
(its critical point is in \((1.38,1.40)\), and use symmetry).
Integration by parts bounds the later oscillating integral
above by \(1/(2\pi)\). The checker verifies the strict
bounds with rational logarithm enclosures.

Put \(q_0=4/3\). Cauchy and Plancherel, splitting at
\(R=.69,.78\) for \(j=4,6\), give
\[
 \int_{\mathbb R}|\widehat g_j(\xi)|\max(t^{q_0},|\xi|^{q_0})\,d\xi
      < J_j,\qquad (J_4,J_6)=(50,83),\quad0<t\le.021 .
\]
Use \(\|g_j\|_2\) below the split and \(\|g_j''\|_2\)
above it; their squares are rational elementary integrals.
Scaling \(\Phi_t\) and applying (9) at \(c=1-t\), the
ordinary absolute angular error after the tag \(dt/t\) is
at most
\[
 \frac{10}{2\pi(1-b)}
 \left\{\frac{44J_4(b^{4-q_0}-a^{4-q_0})}{4-q_0}+
         \frac{112J_6(b^{6-q_0}-a^{6-q_0})}{6-q_0}\right\}.
\]
To upper it opposite a real prime, truncate true ranks and
positive floor by §1, and apply the
[actual \(3.446\) angular prime bound](../angular_prime_first_composite/Proof.md)
to the resulting compact positive source, then take the
physical limits. The positive all-rank integral majorizes
every truncation. The product with \(3.446\) is \(<.115\).
In both orientations we have therefore established
\(-\langle\Pi,kH\rangle\ge(.697-.115)M+o(M)\).

## 4. Multiplicities and the ordinary marked source mass

The prime-weighted four-mark excess
\(\langle\Pi,\binom{k}{4}|H|\rangle/M\) has upper
\[
 \frac{3.446\cdot10}{2\pi(1-4b)4!}
   \int_{\mathbb R}|\widehat F(\xi)|\max(1,|\xi|^{4/3})
                          \min(.01|\xi|,1.4)^4\,d\xi<.021.
                                                                    \tag{10}
\]
Indeed unordered actual designated marks give \(1/4!\),
each contributes \(\int_a^b a_\xi(t)dt/t\le
\min(.01|\xi|,\,2\log 2)\), and the residual total is at
least \(1-4b\). Use (9) and the same prime domination as
in §3, with actual tails justified by §1. For the numerical
norm extend \(F\) on \(-3\le w\le0\) by
\((1-v)^5\sum_{i=0}^4 c_i v^i\), \(v=-w/3\), where the
\(c_i\) are the first five Taylor coefficients of the
polynomial continuation \(F(-3v)/(1-v)^5\).
Set it zero below \(-3\). This is \(C^3\), and integration
by parts bounds each derivative jump of order \(j\) at the
three endpoints by its absolute value times \(|\xi|^{-j-1}\).
The checker takes the minimum with a direct \(L^1\) bound,
uses \(\xi=z^3\) above 1, and computes rational outward
rectangles with an explicit power tail.

Pointwise \(3W\ge-kH-4\binom{k}{4}|H|\), since for
\(k\ge4\) one has \(k\le4\binom{k}{4}\). This proves the
true rebate in (2), with no uniqueness assumption on tags.

The ordinary signed mass is \(M_{kH}/M=-m_*+o(1)\).
For this use direct integer CRT at the actual \(pd\le N^{.52}\)
without any seam modification; the floors after opening true
units cost \(N^{.52+o(1)}\) times fixed logs. The ordinary signed
\(\mu(d)/d\) first-log moment at mask \(Np\) is \(-Np/\varphi(Np)\),
so after the outside factor \(\varphi(N)/(Np)\) the mark
weight is \(1/(p-1)\). The reductions at §1 also apply to
this ordinary unopposed sum.

In the marked ordinary positive mass \(M_{k[H]_+}\), ranks
4–7 are nonpositive: for rank 4 use
\(q\ge t^2+(1-t)^2/3>11/35\); the other signs follow from
(4)–(6). Even higher ranks vanish. Rank 2 contributes
at most \((b-a)(1+39b)/(1-b)\).
On rank 3 without a giant the other two angles are at least
\(1/2-t\), in an ordered interval of width at most \(t/2\);
the score is at most \(1-F(t)\le t+39t^2\).
With a giant write the other small angle as \(u\), so
\(H_3=\int_0^t(F'(u+v)-F'(v))\,dv\). For \(u\le.21\)
this is nonpositive because \(F'\) decreases then increases,
\(v\le.02\), and \(F'(.23)<F'(.02)\).
For \(u>.21\) bound its positive derivative difference by
\([F'(u+.02)-F'(.02)]_+\). The checker integrates this
over \(.21<u\le.49\) with the rational majorant
\(du/[u(1-.02-u)]\); include the nongiant bound above.

For odd \(r\ge9\), differentiate the largest \(r-5\) or
\(r-7\) uniforms for the two derivatives in (5) of higher
order. Bound the remaining density by its largest inverse
length. This gives
\[
 |H_r|\le1056\,2^{r-5}\prod_{i\le4}u_{(i)}
           +80640\,2^{r-7}\prod_{i\le6}u_{(i)} .
\]
Each product of the least \(j\) angles is at most the
designated tag \(t\) times the least \(j-1\) residual
angles. This cancels the mark harmonic denominator \(t\).
For the remaining \(s\)-angle ordered simplex of total one,
use successive ratios \(T_i=u_{(i)}/u_{(i+1)}\).
Its harmonic measure is \(\prod_{i<s}dT_i/T_i\), by the
triangular log projective change and simplex normalization.
The product of the least \(j\) angles inserts
\(\prod_{i<s}T_i^{\min(i,j)}\) divided by
\((1+T_{s-1}+T_{s-1}T_{s-2}+\cdots)^j\).
Keeping the last \(\ell\le s-j\) ratios in the denominator
bounds this weighted angular integral by
\[
 \frac{\mathbb E(1+V_1+V_1V_2+\cdots+V_1\cdots V_\ell)^{-j}}
      {(j-1)!\,j^{s-j}},
 \qquad V_i\text{ independent with density } jv^{j-1}.
\]
Residual total \(1-t\) adds only \((1-t)^{j-1}\le1\).
Use \((j,\ell)=(3,5),(5,3)\) and sum the two geometric
tails starting at \(r=9\); the expectations are bounded
by positive rational cube boxes in the checker. The ordinary
positive mass from ranks 2, 3, and \(\ge9\) is at most
\(.01817,.02177,.04576\), respectively. With the signed
ordinary mass and \(W\le k[-H]_+/3\), this gives
\(M_W\le(.261+o(1))M\).

Finally (3) gives \(\langle W,H\rangle,\langle H,W\rangle
\le(.261-.165)M+o(M)\). Expand \(H_2=H+Q+W\), use (7)
for the entire rough-only debit, and retain all three overlaps
involving \(W\) precisely as in (2).
The [rational checker](check.py) verifies the quoted constants.
