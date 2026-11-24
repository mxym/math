# Same-reflection no-pair dichotomy between the CQ positive block and its prime crosses

This is an inequality on **actual same-N rows**, not the earlier CRT relaxed law. P denotes the actual positive rank2/3 CQ score at floor a=.123, Π the true prime logarithm, J any fixed compact central interval, M=|J|N𝔖(N), L=log N. Both orientations use precisely x+y=N and actual gcd(x,N)=1; J need not be symmetric. Assume R_J=⟨Π,Π⟩=0 whenever the no-pair denominator below is used. Use the calibrated genuine DHR and linear sieve bounds in [WiderPositiveBlock](cubic_quintic_sharp/WiderPositiveBlock.md) (reference commit 989aea5). Put
\[
u=\frac{\langle P,\Pi\rangle+\langle \Pi,P\rangle}{2M},\qquad t=\langle P,P\rangle/M,
\quad p=m(P),\quad q=m(P^2/L),
\]
and fixed safe constants k=4.4784588, U=4.651445, C=20.881873 from that file. The physical two-direction constraint is
\[
\boxed{\qquad
\frac{2(kp-u)^2}{C-2k}-Uq+\frac{u^2}{U}+o(1)\ \le t \le\ Uq-\frac{u^2}{U}+o(1).
\qquad}
\]
This is a target-dependent dichotomy; it adds no extra credit to the old exterior budgets.

## Actual occupancy and the two factors of two

Let Ω be the **single** literal ambient of true reflected pairs with both squarefree, least factors >N^.123, and true target units. Normalize its counting measure μ by M/L². Define binary i_x=1_{x prime} and i_y similarly, and f_x=P(x)/L, f_y=P(y)/L. Both amplitudes are between 0 and 1 and vanish at their own prime flags, exactly. The ordinary sieve weight conversion log n/L=1+O_J(1/L) is uniform; all relevant Ω measures already O(1) by the genuine caps. Thus t=∫ f_x f_y dμ exactly and u=1/2∫(f_x i_y+f_y i_x)dμ+o(1).

Write r_x=∫i_x, r_y=∫i_y. These are each between k+o(1) and U+o(1). Both are counts in the **same Ω**, not two ambient estimates: the genuine actual rank-one (prime) source has mean count harmonic 1, and its literal opposite is sieved at floor .123 with actual target units, while source prime already rough/squarefree. Lower/upper rank-one estimates at k/U are explicitly included in WiderPositiveBlock. Reflecting the interval for the reverse gives same N and J-length, hence same k/U. With R_J=0, i_x i_y=0 on Ω, so its true composite-by-composite mass c₀ is μ(Ω)−r_x−r_y ≤ C−2k+o(1). The lower ambient from WiderPositiveBlock gives c₀≥20.7916331−2U+o(1)>0. Without R_J=0 the same exact occupancy count adds μ(i_x i_y)=R_J/M+o(1), so the lower bound version can instead use denominator C−2k+R_J/M+o(1); we do not infer disjointness when a pair exists.

On Ω the first moments of each f arm are ≥ kp+o(1) by the literal rough marginal lower for the compact positive source P. On Ω_cc (the composite subset) their sum S is ≥2kp−2u+o(1): the deleted prime-sided rows remove only the two mixed terms f_x i_y,f_y i_x because f vanishes on its own prime. Also u≤U+o(1) by f≤1 on the two opposite prime occupancies, so kp−u stays positive uniformly. Each untrimmed second moment is ≤Uq+o(1) by applying the same compact rough upper to P²/L, a nonnegative fixed-rank genuine source, with no sign cancellation. In removing the prime-sided rows, Cauchy on the two directions together (count the prime-side sets in their respective orientations) gives
\[
\int(f_x^2i_y+f_y^2 i_x)\,d\mu
\ge \frac{[\int(f_x i_y+f_y i_x)\,d\mu]^2}{r_x+r_y}\ge 2u^2/U+o(1).
\]
Thus the actual total composite second moment D is ≤2Uq−2u²/U+o(1). The factor 2 here is the square (2u)^2 divided by the summed prime occupancy ≤2U, not two independent nonmeasured means.

On Ω_cc, Jensen/Cauchy for the **single sum** f_x+f_y yields
\[
D+2t=\int (f_x+f_y)^2d\mu\ge S^2/c_0\ge 4(kp-u)^2/(C-2k)+o(1).
\]
No PP terms occur outside Ω_cc, since P zero on primes. Subtract D and divide by 2, giving the asserted left inequality. For the right, 2t≤D by (f_x−f_y)²≥0. This uses actual two-arm same-target data even with nonsymmetric J; no assumption about equality of the two mixed crosses.

## Exact ordinary amplitudes and strict margins

At a=.123, c=1−3a, w(t)=1−2(1−2t)^3+(1−2t)^5, the one-arm p is
\[
2\log(2(1-a))+\tfrac12-8a^2(1-a)^2+\tfrac43c^2\{3-5(3a^2+2ac+c^2/2)\}
=2.062403475748649\ldots.
\]
Rank2 uses ordered least-angle harmonic dt/[t(1−t)]; w/(t(1−t))=2/(1−t)+16t−48t²+32t³. Rank3 amplitude 16∏u_i(3−5Σu_i²) cancels harmonic denominator, divide unsorted simplex by 3!, and use uniform simplex mean Σu_i² after affine map u=a+c z. These are ordinary moments, not a substitution for paired target moments.

For q₂ rank-two square contribution, divide polynomial W(t)^2/t (W=w) as [W(t)^2/t−4]/(1−t)+4/(1−t); numerator vanishes at t=1 since W(1)=2. Integrate the polynomial rationally on [a,1/2] plus 4log(2(1−a)). For q₃ rank-three square contribution use
\[
q_3=\frac{256c^2}{3!}\int_{z_1,z_2\ge0,\ z_1+z_2\le1}
\prod_i(a+cz_i)\big(3-5\sum_i(a+cz_i)^2\big)^2 dz_1 dz_2,qquad z_3=1-z_1-z_2.
\]
After expanding the polynomial, each monomial z₁^i z₂^j z₃^k integrates exactly i!j!k!/(i+j+k+2)! by two beta integrals. Rational expansion gives q₃≈.2741244329628132; q₂ with 10-term atanh for log from x=2(1−a) gives 1.27141433097953<q₂<1.27141433098017; sum lies between 1.545538763942 and 1.545538763944. This was replayed as exact rational coefficient convolution and simplex factorial sums (not quadrature). Thus safe rounded p>2.0624, p<2.0625, q<1.54554 throughout. Since fixed J log factors change only O(1/L), no separate H-square amplitude correction.

At u=1.05 the conservative lower using p=2.0624,q=1.54554 is 4.287770627535176. This quadratic lower decreases on [0,1.05] (derivative at right −2.294491… and derivative increases). Hence at sufficiently large no-pair targets:
- **Either u>1.05 or t>4.28**. In particular if actual PP≤p²M (ordinary independent leading product p²<4.25391), then the mean of the two genuine mixed prime crosses exceeds 1.05M, instead of just the [separately proved](CQActualMixedPrimePositiveBlock.md) ≥.146M under no-pair.
- If actual t≥5.174 then u<3.0624<p+1 for large N: with u≥3.0624 the upper t≤Uq−u²/U is <5.173+o(1) by exact rounded constants (5.17278348…).

Do not infer u≤1.05 from the existing unconditional positive-block lower, nor PP≤ordinary product at a hypothetical exception. The first dichotomy excludes a **joint combination** of small mixed crossings and merely ordinary-sized PP. The second sets a measurable coupled threshold, but present guaranteed PP>1.2976 is far below it. At u≈p+1 and PP≈p²−1 the numerical coupled strip alone is still compatible, so no closing of the full exterior nor contradiction to no-pair. Existing true .146 lower and 4.300 upper on individual crosses stay useful separately.
