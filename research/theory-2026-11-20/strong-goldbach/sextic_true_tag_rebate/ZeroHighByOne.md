# The zero-by-one chamber with at least four factors on the zero-tag arm

Keep the fixed even \(N\), central interval \(J\), unit pairing, logarithm \(L=\log N\), and \(M=|J|N\mathfrak S(N)\) of the [full zero-tag pair](ExactDHRZeroTag.md). Keep the exact sextic \(S=G_b+W\), \(b=.003\), and the tag threshold \(a=.080\). A tag is an actual prime in \((N^b,N^a]\). Only \(N^b\)-rough arms are scored.

**Proposition.** On the entire actual zero-by-one chamber with at least four prime factors on the zero-tag arm, including both orientations, the signed sum exceeds \(-.092M+o(M)\). Both signs and every rank on the one-tag arm are included. The earlier [medium semiprime by one-tag chamber](MediumSemiprimeOneTagAdverse.md) is untouched. The zero-by-one exterior with a genuine rank-two or rank-three zero-tag arm is not priced here.

## 1. Two-sided signed reception of the whole one-tag arm

Let \(X\) be \(S\) on the actual one-tag arm, zero elsewhere. There \(S=H\): the other factors are all \(>N^a\), and the original \(Q,W\) both vanish. Scores on nonsquarefree rows vanish. If the unique tag is \(p\), of angle \(t=\log p/L\), write the arm \(p m\). The genuine expansion is
\[
 X(pm)/(Lt)=\sum_{d\mid m}\mu(d)g_t(\log d/L)+o(1),
 \qquad g_t(s)=(F(s)-F(s+t))/t\ge0.
\]
This is the same bounded-factor, bounded-positive-floor normalization as in the [one-tag self-pair](FullOneByOneTagCredit.md). Its true squarefree restoration and the replacement of own logarithms by \(L\) have \(o(M)\) cost. The positive model densities of the actual even and odd divisor labels are denoted \(E(s),O(s)\); these are the ordinary (unopposed) densities, not conditional pair counts.

Let \(Z\) be a compact nonnegative genuine prime-product source on the \(N^a\)-rough opposite arm, and let \(\mathsf m(Z)\) be its ordinary mass normalized by its interval length. Assume \(Z\le K L\). The following bounds apply in either true reflected orientation:
\[
 \begin{split}
 \langle Z,X\rangle/M &\ge -1.275137\,\mathsf m(Z)-.00245645 K+o(1),\\
 \langle Z,X\rangle/M &\le -.2407793\,\mathsf m(Z)+.00245378 K+o(1).
 \end{split}                                                     \tag{1}
\]
To prove them, tile the actual tag angles by .0002 cells and the nonunit divisor angles by .0001 cells. Use the separate unit atom \(d=1\). On nonunit cells with \(t_++s_+\le.490\), at actual level \(N^{.499-t_+-s_+}\), apply ordinary product-BV and the exact linear sifting functions of [the linear refinement](ExactLinearZeroTag.md#the-entire-genuine-prime-cross). The modulus literally divides a product \(p d\ell\) of size at most \(N^{.499}\). As in the existing true one-tag transfer, use residue \(N\), reduced model, and target and named-prime exclusions. A prime at most \(N^a\) has density \(1/(p'-1)\) unless excluded; the actual tag is omitted from the inner sifting primes and its square is restored as an error, of fixed power saving because \(p\ge N^{.003}\). The same actual product-BV and square controls apply to \(Z\). The normalized coefficients for the real linear lower and upper at exponent \(D=.499-t_+-s_+>0\) are \(k(D),U(D)\). Combine the genuinely nonnegative counts before subtraction: the signed lower and upper per cell are respectively
\[
  g_t(s)(kE-UO)\,\mathsf m(Z),
  \qquad
  g_t(s)(UE-kO)\,\mathsf m(Z).
\]
The even atom uses \(k(.499-t_+)\) and \(U(.499-t_+)\), respectively. Integrate with actual tag harmonic \(t/p\), so the exponent measure for that harmonic is \(dt\). Signed enclosure must be integrated before using the sign of the upper coefficient.

For the remaining nonunit cells fix the actual \(p,d\) with \((pd,N)=1\). Sift both coordinates of the literal fibre \(x+pd r=N\), with \(x,r\) genuinely \(N^a\)-rough and use \(Z\le K L\). Its free length is \(|J|N/(pd)\), with actual remainder for an opt-in sieve modulus \(\ell\) of \(O(2^{\omega(\ell)})\). The dimension-two positive Selberg square with support \(N^{.499(1-t_+-s_+)}\) gives, in the usual \(M/(pd L^2)\) scale, coefficient
\[
 C_2(t_++s_+)=\left[
 a^2\mathcal G\bigl(.499(1-t_+-s_+)/a\bigr)\right]^{-1},
 \quad\mathcal G(u)=\int_0^u\rho_2(v)\,dv,
\]
as in the [physical affine sieve](FullZeroTagAffineSelf.md#2-the-genuine-dimension-two-lower-and-upper-on-the-same-fibre). Its support-square error is power-saving uniformly because \(t_++s_+\le .58\). At \(p'\mid N\) the two roots coincide, at \(p'=p\nmid N\) the left arm is the target unit and there is one \(r\)-root, otherwise there are two roots below \(N^a\). The single extra local factor at \(p\ge N^{.003}\) is \(1+o(1)\). Named divisor factors exceed \(N^a\); the upper can drop any further unit restriction. Consequently the positive absolute cap on the even tail is \(K\int g_t(s)E(s) C_2(t_++s_+)\,ds\,dt\), and on the odd tail it is the analogous expression with \(O\). For the lower in (1) charge only the odd remainder and for the upper only the even remainder. The attached outward checker reuses the audited \(g_t\), linear-delay and Selberg denominator functions by hash. It gives coefficients \(-1.27513611138283\), \(-.24077934796583\) and even/odd caps \(.00245377266172\), \(.00245644180917\), with the rounding in (1).

## 2. Genuine zero-arm sign budgets

Let \(A_+\) and \(A_-\) be the positive and negative parts of the zero-tag score restricted to ranks 4 through 7. Thus \(A_-\ge0\) as a magnitude. The positive part occurs only in rank 4, and on that rank its pointwise bound is \(.422L\) by \(\sum v_i^2\ge1/4\) and \(\prod v_i\le1/4^4\) with actual own-log angles \(v_i\). The negative magnitude is at most \(1.25L\): at given largest angle \(u\), bound \(\sum v_i^2\le u\) and \(\prod v_i\le u((1-u)/(r-1))^{r-1}\) at ranks 4 and 5 and use the original rank formulas and rank-five coefficient \(10080\sqrt q-1056/\sqrt q\). The checker covers \(u\in[1/4,.760]\) and \(u\in[1/5,.680]\), respectively, with rational .001 cells. The rank-five product uses its left endpoint, since \(u((1-u)/4)^4\) decreases for \(u\ge 1/5\). Rank 6 has cap \(40320/6^6\). At rank 7 use
\[
 2112/7^4+80640\sqrt{14}/7^7<1.25:
\]
the original box derivative bound controls the first term, and Ball's bound \(b_7(0)\le \sqrt{2/\sum v_i^2}\le\sqrt{14}\) controls the second. The slight change between actual own-log floors and \(a\) is absorbed by strict margins.

The ordinary positive rank-four mass \(\mathsf m(A_+)\) has upper \(.061684801406559\) and lower \(.056073385765959\). After the actual angular harmonic denominators cancel, integrate \((528-1680q)_+\) on the ordered simplex \(v_i\ge a,\sum v_i=1\), where \(q=\sum v_i^2\). Sort the first three coordinates and use the exact 512-subdivision grid of the interval of excess \(1-4a\). Sum over potentially ordered boxes for an upper; the tangent of the convex quadratic \(q\) at each center gives its lower enclosure throughout the closed box. For a lower sum take only boxes satisfying the full last-coordinate order and use the vertex maximum of \(q\). Divide by equal-cell factorials of the first three coordinates to retain their order; the arithmetic is exact rational outward. Its signed rank-four mean is
\[
 (528-1680[4a^2+2a(1-4a)+2(1-4a)^2/5])(1-4a)^3/(4!3!).
\]
For the actual rank-five signed mass use \(b_{k,a}=\kappa_a^{*k}/k!\), where \(\kappa_a(dt)=1_{t>a}\,dt/t\), and \(\psi(s)=F(s)-F(1-s)\). Pair each real divisor with its complement in odd rank five. The mass is exactly
\[
 b_{5,a}(1)-\int\psi(s)b_{1,a}(s)b_{4,a}(1-s)\,ds
                 +\int\psi(s)b_{2,a}(s)b_{3,a}(1-s)\,ds .
\]
Here the integrals are only on their true compact positive-floor supports; the unit atom accounts for the first term. The checker uses the ordinary positive harmonic recurrence \(t b_{k,a}(t)=\int_0^{t-a}b_{k-1,a}(v)\,dv\) for \(k>1\), with \(b_{1,a}(t)=1_{t>a}/t\), to enclose the signed mean on the \(10^{-4}\) mesh. It lies below \(-.0877432\). All rank-five and rank-six terms are nonpositive. The rank-six negative mass is exactly \(40320(1-6a)^5/(6!5!)\). For rank seven \(b_7(0)\ge1\) by unimodality and support length one, and \(b_7''(0)\le0\); the exact rank-seven expression therefore gives a negative magnitude at least \(80640(1-7a)^6/(7!6!)\) after the angle products cancel. Subtract the whole \(\mathsf m(Q)<.01701\) for the original clipping, which can only decrease the negative mass. Together these yield \(\mathsf m(A_-)>.16332506\).

The remaining zero-tag ranks can only be 9 and 11: the even ranks from 8 vanish and \(13a>1\). Their total ordinary absolute mass is bounded by
\[
 m_h=\sum_{r=9,11}
 \left(\frac{1056\,2^{r-5}}{r^4}+\frac{80640\,2^{r-7}}{r^6}\right)
 \frac{(1-r a)^{r-1}}{r!(r-1)!a^r}
 <.000061221
\]
using the [true high-rank half-envelope](../sextic_four_small_high/HalfEnvelope.md) and AM--GM on the actual least angles. To receive those high zero arms, the whole one-tag arm has genuine absolute receiver smaller than \(36\). Use the ratio-four true linear upper \(.575/a\) with the named tag opened. The exact low cap of [the one-tag proof](FullOneByOneTagCredit.md#3-outward-replay-including-every-remaining-physical-rank) is \(15.4\) in normalization \(Lt\). For quotient ranks \(k=8,10,12\), the same proof's high cap is at most \(1056\,2^{k-5}/k^3+80640\,2^{k-7}/k^5\). This is \(<90\) for all, and \(<41\) when \(t>.04\) since then \(k=12\) is impossible. The actual reciprocal harmonic again leaves \(dt\), giving \((.575/a)(.037\cdot90+.040\cdot41)<36\) for the whole absolute receiver.

## 3. The literal chamber and previous overlaps

Apply the lower in (1) to \(A_+\), and subtract the upper in (1) with \(Z=A_-\). Thus the adverse cost in one orientation is bounded by
\[
 1.275137\,\mathsf m(A_+)+.422(.00245645)
     +1.25(.00245378)-.2407793\,\mathsf m(A_-)+36m_h .
\]
The same proof applies on \(1-J\), giving total cost at most \(.091278101M+o(M)\) and the strict stated \(.092\) bound. This includes the entire signed chamber and does not discard favorable rows.

All counts other than zero-by-one are disjoint. The prior early one-tag and zero-tag-semiprime chamber is also disjoint by actual rank. To combine with the old tagged chamber, conservatively remove both old \(01\) witnesses using [the exact old grid mask](TaggedCreditOutsideZero.md), even though not every old \(01\) row has zero-arm rank at least four. Old \(01\) rows outside rank at least four return to the unpriced residual if not elsewhere paid. The two old \(02\) witness orientations may retain \(.0003109790613-.000176>.00013\), charging the same full old adverse tail once. This is a literal support contraction, not a binary lower bound.

Run:

    python3 -OB check_zero_high_by_one.py
