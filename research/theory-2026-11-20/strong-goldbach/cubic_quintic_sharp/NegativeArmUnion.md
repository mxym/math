# Signed removal of every cubic–quintic negative arm above .105

Use the exact physical score \(H=V-\Pi\) of [the sharp cubic–quintic detector](CubicQuinticSharp.md):
\[
 F(t)=2(1-2t)_+^3-(1-2t)_+^5,\qquad
 V(n)=\mu^2(n)\log n\sum_{d\mid n}\mu(d)F(\log d/\log n).
\]
Keep the original individual even \(N\), \(x+y=N,\ x\in NJ,\ (x,N)=1\), reflected interval \(1-J\), \(L=\log N\), \(M=|J|N\mathfrak S(N)\), and actual \(R_J=\langle\Pi,\Pi\rangle\). No prime or nonsquarefree argument has nonzero \(H\).

Let \(\mathcal P\) be the actual pairs on which **both** arguments have true rank 2 or 3, are squarefree, and have all actual factors \(>N^{.150}\). Every score on these rows is positive, and the genuine positive-only rank-2/3 proof in §4 of the sharp detector gives \(>.575485M+o(M)\) on \(\mathcal P\). Let \(\mathcal A\) be the actual pairs on which **at least one** argument satisfies \(H(n)<0,\ P^-(n)>N^{.105}\); the other argument is arbitrary. These two sets are disjoint by their literal signs.

**Theorem.** The complete signed contribution on \(\mathcal A\) is greater than \(-.493039M+o(M)\); in particular
\[
 R_J\ge .082M+\sum_{(x,y)\notin\mathcal P\cup\mathcal A}H(x)H(y)+o(M).
 \tag{1}
\]
Every adverse row still in this exterior has a genuine least factor \(\le N^{.105}\) on its **negative** arm. No sign or lower bound is asserted on the signed exterior.

There is an alternative on a larger exterior. Keep the earlier \(>.515M\) lower on the entire both-\(.150\)-rough chamber, and remove only the union \(\mathcal A_{\rm mid}\) where some negative arm has actual least prime in \((N^{.105},N^{.150}]\). Its signed contribution is \(>-.414666M+o(M)\), disjoint from the earlier rough chamber, leaving \(>.1003M\) before that larger signed exterior. This alternative does not remove all negative \(.150\)-rough arms with small-factor opponents. The two comparisons are not added: (1) uses only the original positive rank-2/3 block, not the whole \(.515M\) block.

## 1. Actual signed transfer against a compact source

For a bounded fixed-rank product source \(Z\) supported on a fixed positive power floor, whose normalized amplitude is a bounded piecewise continuous function of its literal prime angles and the central spatial variable, with \( |Z|\le |H|\) for the sharp comparison, its ordinary mass \(m(Z)\) is in units \(|J|N\). For the actual sources below it is independent of the choice of \(J\) or \(1-J\) of the same length. True prime-product distribution gives
\[
       \langle Z,H\rangle=2m(Z) M-\langle Z,\Pi\rangle+o(M),
 \tag{2}
\]
and the reflected direction. In particular (2) holds for the actual positive weight \(Z=[-H]_+\) on any of our rank and least-factor cells. Here the prime term is on the other integer in the **same fixed-target pair**, not an independent prime-density normalization.

For exactness, use the fixed own-log smooth taper of the sharp detector and its actual squarefree CRT/BV reduction. The sharp-to-taper difference on this paired source is \(O(h^{3-c}M)\) with \(c=4/\pi+\epsilon<2\) in its Fourier envelope, since the present sources are bounded by \(|H|\). A fixed smooth taper is replaced by its target-log counterpart at \(o(M)\), and its square label is truncated as there. Every actual opened modulus \([d,e^2]\) has exponent strictly below \(1/2\), with fixed divisor-power multiplicity. On each genuine compact finite-rank source one labels true factor slots, selects one true prime slot and groups the others; ordinary product BV applies to those actual source coefficients at the literal reduced residue \(N\). One can use log-fine cell boxes in the independent factors and smooth angular approximations, exactly as in §4 of the sharp detector's genuine receiver. The sign part and the actual least labels are retained; they are continuous amplitudes or interval cuts on compact genuine angle boxes. True boundary strips are removed with the same positive rough bounds, and only after the signed completed estimate may the smoothing be refined.

In the reduced model the mask is \(Nx\) at the actual \(x\) in the source. Its large source primes only change the singular coefficient by \(1+o(1)\) uniformly, since there are boundedly many of them and each exceeds a fixed positive power. The squarefree completion and the first-log moment are the one-arm local ones in §2 of the sharp proof, with this polynomial mask. The zeroth moment vanishes; the coefficient is \(-F'(0)=2\), not the sextic coefficient. Then \(N\to\infty\) first and \(h\downarrow0\) gives (2). Genuine primes are unchanged by the taper. All ordinary masses used here are nonnegative, and \(\langle Z,\Pi\rangle\ge0\) on our nonnegative sources.

For any such magnitude \(A\ge0\) supported on a set where \(H=-A\), and zero elsewhere, the actual signed union where at least one arm has \(A>0\) is
\[
  -\langle A,H\rangle-\langle H,A\rangle-\langle A,A\rangle
  \ge -4m(A)M-\langle A,A\rangle+o(M).
 \tag{3}
\]
The subtracted overlap is a genuine positive score product on which both originally negative arms occur. It is priced below by a true upper, not by removing a lower credit. The omitted \(+\langle A,\Pi\rangle+\langle\Pi,A\rangle\) terms are nonnegative; no further estimate on them is used. Since \(A\) is composite-only this calculation inserts no copy of \(R_J\).

## 2. Real ordinary cap and mass on the negative band

Put \(a=.105,\ b=.150\), and let \(A_r\) be \(A_{\rm mid}\), the **magnitude** of the exact negative score on least prime in \((N^a,N^b]\), restricted to actual rank \(r\). Only \(r=3,4,5,6,8\) can contribute: ranks 1,2 are nonnegative, rank 7 or 9 is odd and zero by the exact global formula, and \(10a>1\). True squares have zero score. All angle calculations here use own log; the target-log cut differs by \(O_J(1/L)\), with actual fixed-rank collar costs tending to zero by the original true rough count and angular source argument. Use outward closed bins for each upper, so literal endpoints do not contribute an uncontrolled atom.

At rank 3 the negative weight after cancellation of the harmonic denominators is \(16(5q-3)_+\), \(q=\sum u_i^2\). Let \(w\) be the largest genuine angle. Negativity first gives \(w>(1+1/\sqrt5)/2\) by \(q\le w\) for \(w\le.5\) and \(q\le w^2+(1-w)^2\) otherwise. With every angle \(\ge.1\), the upper at fixed \(w\) is \(2w^2-1.8w+.82\), by setting one other angle to \(.1\) and the other to \(.9-w\). It is increasing on this range and below \(.6\) at \(w_0=.754\). Thus \(w>w_0\), \(5q-3\le7(w-w_0)\) since \(w\le.8\), and \(5q-3\le.3\). The pointwise negative cap is \(16w_0((1-w_0)/2)^2(.3)<.055\), because \(w(1-w)^2\) decreases for \(w>w_0\). At fixed \(w\) the lesser angle in the ordered simplex has interval length at most \((1-2a-w)/2\). Hence the ordinary negative band mass is at most
\[
  56(1-2a-.754)^3/6 .
\]
The angular floor \(>b\) would give no negative rank 3 anyway.

At rank 4 use the exact folded formula from §4 of the sharp detector. With the whole actual angle in each least-angle bin of width \(.001\), the checker covers the first three sorted angle cells and all possible fourth angles \(w=1-u_1-u_2-u_3\) with \(w\ge u_3\). Using \(G_0(t)=2|1-2t|^3-|1-2t|^5\), upper-round the four singleton values and lower-round the three pair values of that formula. The lower pair value is zero when its interval straddles half. Divide the cell upper by the product of the four lower angle endpoints for the ordinary mass. This same interval bound gives a pointwise negative cap \(c_{4,i}\) on each least bin \(i\). In the outer mass upper allowing an entire cell that meets the sorted domain can only overcount, and no extra factorial reduction is required at equal bins. The exact outputs are \(m(A_4)<.041409576\) and every \(c_{4,i}<.218\).

At rank 5 the exact negative weight \(1920\prod u_i\) cancels all ordinary harmonic denominators. The band mass is
\[
 \frac{1920\{(1-5a)^4-(1-5b)^4\}}{5!4!}.
\]
At least angle \(t\) the pointwise cap is \(1920t((1-t)/4)^4\), increasing for \(t\le b\), by the AM–GM bound on the remaining angles.

For ranks 6 and 8 let \(b_r\) be the density of the centered sum of independent uniforms of the actual widths \(u_i\), a finite-difference representation, not a model of physical prime factors. The exact normalized expression is
\[
    \left(\prod u_i\right)
         \{96 b_r^{(r-4)}(0)-3840 b_r^{(r-6)}(0)\}.
 \tag{4}
\]
Indeed the profile is \(16(1/2-t)_+^3-32(1/2-t)_+^5\). Its fourth/sixth distributional derivatives at half give the displayed coefficients; the finite difference for even rank has positive outside sign. The derivative terms in (4) can also be obtained by applying the fundamental theorem \(r\) times to the original actual divisor sum, then smoothing the two truncated powers and passing to the continuous remaining box densities.

Use [Ball's cube-slice bound](https://doi.org/10.1090/S0002-9939-1986-0840631-0), \(b_j(0)\le\sqrt{2/\sum u_i^2}\) for the surviving \(j\) uniform widths. These box densities are symmetric and unimodal. Differentiating the \(k\ge1\) largest factors gives \(2^k\) signed translates of the remaining nonnegative density with equal positive and negative multiplicity; their absolute difference is at most \(2^{k-1}\) times its maximum. The product of the remaining \(j\) lengths, times that maximum, is at most
\[
 \sqrt{2j}\,S_j^{j-1}/j^j\le\sqrt{2j}(j/r)^{j-1}/j^j
\]
by AM–GM and \(S_j=\sum_{i\le j}u_{(i)}\le j/r\). For \(k=0\) the same formula uses all \(r\) angles. This bounds the absolute rank-6 and rank-8 scores respectively by
\[
 \frac{192\sqrt8(4/6)^3}{4^4}+\frac{3840\sqrt{12}}{6^6}<.915,
 \quad
 \frac{768\sqrt8(4/8)^3}{4^4}+
           \frac{7680\sqrt{12}(6/8)^5}{6^6}<1.2 .
\]
For the ordinary rank-6 mass improve over using the cap divided by \(a^6\). The two longest factors obey \(u_{(5)}u_{(6)}\ge1/36\): \(w=u_{(6)}\in[1/6,.5]\), \(u_{(5)}\ge(1-w)/5\), and \(w(1-w)\) is increasing there. In (4) this bounds \(|b_6''|\le 72 b_4(0)\le72\sqrt{1/2}/a\), and \(b_6(0)\le\sqrt{12}\). Cancel the ordinary harmonic factors and integrate the remaining constant over the **whole** ordered \(a\)-rough simplex with volume \((1-6a)^5/(6!5!)\) for an upper. For rank 8 use the cap \(1.2\) times \((1-8a)^7/(8!7!a^8)\); this includes every actual rank-8 sign. The checker gives the following ordinary uppers, displayed rounded upward:
\[
\begin{array}{c|ccccc}
 r&3&4&5&6&8\\ \hline
 m(A_r)&.000435456&.041409576&.031333594&.004803514&.000001073 .
\end{array}
\]

## 3. The actual band receiver and both genuine overlaps

Let \(Z\) be a nonnegative compact product source as in §1. For the actual band receiver \(A_r\), open its **unique least prime** \(p\) of angle in bin \(i\), \(t_-\le\log p/L\le t_+\). Its remaining literal quotient is \(N^{t_-}\)-rough, and we may discard the rest of its rank and sign restrictions only after using its recorded pointwise cap \(c_{r,i}L\). Use true product BV on \(Z\) and a linear upper on that quotient at level \(N^{D_i}\), \(D_i=.499-t_+\). Every physical tested modulus is \(pd\le N^{.499}\), with fixed divisor-power multiplicity. Small own-log versus target-log endpoint collars may be taken infinitesimal with a fixed strict subroot buffer, as in §2. The genuine reduced density is \(1/\varphi(p)\) outside, then the quotient densities \(1/(s-1)\) off \(Nx p\), zero at excluded primes. Omitting \(p\) from the tested small primes is harmless since it is polynomially large. On any actual shared prime between the two named supports, the target-unit constraint forces incompatibility; such rows are not restored. Positive uppers can drop its omission in the reciprocal model. There is no claimed progression estimate for each fixed \(p\); it is one absolutely summed product-source BV error at the literal grouped moduli.

Put \(s_i=D_i/t_-\). In our band \(1<s_i<4\), so the normalized upper coefficient is \(U_i=D_i^{-1}A_{\rm lin}(s_i)\), where
\[
 A_{\rm lin}(s)=
 \begin{cases}
  2,&1<s\le3,\\
  2+\displaystyle\int_3^s \frac{2\log(v-2)}{v-1}\,dv,&3<s\le4.
 \end{cases}
\]
The genuine \(p\)-reciprocal harmonic bin mass is at most \((t_+-t_-)/t_-\) in the limit. The checker encloses \(A_{\rm lin}\) by a rational upper integral on mesh \(1/1000\), with upper endpoint of the logarithm, lower endpoint of the denominator and a positive rational atanh remainder. Thus
\[
 \langle Z,A_r\rangle\le (U_r m(Z)+o(1))M,\qquad
 U_r=\sum_i c_{r,i}U_i(t_+-t_-)/t_- .
 \tag{5}
\]
The same holds with \(J,1-J\) switched. Between actual ranks \(r,j\) we can therefore use the smaller of \(U_r m(A_j)\) and \(U_j m(A_r)\) on **the same physical pairs**, not as a distributional approximation. Summing the two indices, retaining the single diagonal, gives
\[
 m(A_{\rm mid})<.077983212,\qquad
 \langle A_{\rm mid},A_{\rm mid}\rangle <.102732633M+o(M).
\]
Equation (3) now gives \(>-.414666M+o(M)\) for the complete band union. This proves the alternative comparison, using its literal disjointness from the both-\(.150\)-rough chamber, not just disjointness of one-arm weights.

For (1) put \(A_{\rm hi}=[-H]_+1_{\{P^->N^{.150}\}}\). The genuine rank-4,5,6 ordinary bounds from §4 of the sharp proof give \(m(A_{\rm hi})<.00672821\). Its cap is \(.915L\): use the just-proved rank-6 cap, the exact rank-five cap .6144, and the same folded rank-four interval or a simple bound. For the latter, on \(u\in[.15,.55]\) the convex function \(G_0\) has its singleton sum maximized on the extreme tuple \((.55,.15,.15,.15)\); this sum is \(G_0(.55)+3G_0(.15)<1.56\). Dropping the positive pair terms in the exact rank-four formula then gives negative cap \(<.56\). The true \(.150\)-rough opposing upper receiver gives \(U_{\rm hi}=(40/9)\cdot.915\) for the high magnitude against any such compact source, as in the sharp proof.

On the low band, every pointwise cap **except rank 8** is bounded by .915. Thus the entire \(A_{\rm mid}-A_8\) receiver in (5) uses the single constant \(U_6<1.7902\), not a sum of receiver caps (the ranks are mutually exclusive before the pointwise bound). For \(A_{\rm hi}\) versus \(A_8\) use the reflected high receiver \(U_{\rm hi}m(A_8)\). The high-to-high term is at most \(U_{\rm hi}m(A_{\rm hi})M+o(M)\). Combined with (3) the complete signed debit for \(A=A_{\rm mid}+A_{\rm hi}\) on its actual union is bounded by
\[
 4m(A)+.102732633
 +2\{U_6m(A_{\rm hi})+U_{\rm hi}m(A_8)\}
 +U_{\rm hi}m(A_{\rm hi})<.493039 .
\]
The checker uses its exact outward values and proves this strict budget. The two cross terms are genuine reflections, and the high self-pair is not subtracted twice. Only the original positive-only \(.575485M\) block is now inserted. It is disjoint from this complete negative-arm union, since its two physical scores are positive. The sharp identity therefore gives (1) with the stated literal signed residual; no previous whole rough covariance has been added.

Run:

    python3 -OB check_negative_arm_union.py
