# A fixed-target GRH reduction down to square-root logarithmic moduli

This refines the [general top-modulus identity](DirectGoldbachGRHFullTopTargetAtom.md), using only Dirichlet GRH as a zero hypothesis. It is an exact reduction with error smaller than the **reduced** target budget, not an estimate for the remaining sign.

Take the same genuine smooth weights \(w,g\), \(R(N)\), \(I\), and exact delta blocks as before. Put \(X=N\), \(L=\log X\), and choose one sufficiently large **fixed** \(K\). Set
\[
 Q=\sqrt X L^K,\qquad Y=X/Q,\qquad T=\sqrt X L^{3K/4},\qquad M=L^{K/2}.
\]
Take a smooth \(0\le\chi\le1\) vanishing on \([0,1]\) and equal to one on \([2,\infty)\), and write
\[
 \kappa=\frac{c_Q}{Q}\sum_q \chi(q/T) C_{q/Q}\frac{\varphi(q)}q .
\]
Then \(1-\kappa\asymp T/Q\), and for any sufficiently large fixed \(B\),
\[
 (1-\kappa)\big(R(N)-X\mathfrak S(N)I(0)\big)
  =\sum_{T/L^B<q<2T}(1-\chi(q/T))D_q+o(XT/Q).
 \tag{1}
\]
All sums are over physical moduli and true prime vectors in the exact cover. The remaining band is within fixed logarithmic powers of \(\sqrt X\). No assertion is made that its signed sum is large or small enough for positivity.

## 1. The same cover at this scale

Here \(Q^2\gg X\), so the common physical cutoff of the exact delta identity is one throughout the compact prime supports for large \(X\). The support of the prime inputs is larger than every \(q\le Q\). The elementary centered mixed formula and pole/continuous model of the [exact identity](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/ExactDeltaLinearRemoval.md) still apply. The pole error is power-small, by the absolute Rankin sum of the singular coefficients and the uniform first kernel moment on \(q\le Y^{1/2}\), and bounding the tail \(q>Y^{1/2}\) by its Rankin bound. The normalized continuous factor there is \(I(0)+O(q/Y+(q/Q)^A)\). For the mixed blocks, the true prime AP prefix error in each reduced class is \(O(\sqrt X L^{O(1)})\) under GRH. In their smooth test the variation is \(O(1)\) for \(q\le 2Y\); for \(q>2Y\) the kernel is constant and adds the factor \(O(Y/q)\). The divisor formula and the ordinary divisor moments show the sum over both mixed families is \(O(\sqrt X\,Y L^{O(1)})=O(X L^{-K+O(1)})\), negligible relative to \(XT/Q=X L^{-K/4}\) for large fixed \(K\).

For \(q\) in the smooth top weight the exact constant-kernel divisor switch remains valid:
\[
 \sum_q\chi(q/T)D_q
 =\frac{c_Q}{Q}\sum_{m,d}\frac{\mu(m)}m\, V_m(d) H_d,\qquad
 V_m(d)=\chi(md/T) C_{md/Q}.
\]
We use the same true \(H_d\) of unit-centered vectors, with the prefix GRH bound \(|H_d|\ll XL^{O(1)}\) from character Parseval. The terms \(m>M\) cost \(O(X L^{O(1)}/M)\). When \(m\le M\), all retained \(d\ge T/M=\sqrt X L^{K/4}\), up to harmless constants in dyadic cuts. On a dyadic band \(d\asymp U\) absorb a smooth partition into \(V_m\). As a function of \(d/U\) the resulting test \(W\) has uniformly bounded smooth norms of every fixed order, since \(C_x\) has bounded logarithmic derivatives, vanishes near \(x=1\), and \(\chi\) has a fixed ratio transition. This choice avoids estimating a sharp endpoint via a frequency cutoff.

## 2. Smoothed GRH alias switch near the root

For \(|k|\ll X/U\), \(k\ne0\), the actual prime–prime sum on this dyad is
\[
 \sum_{p+p'\equiv N\bmod |k|}
  (\log p)(\log p') w(p/X)g(p'/X)\,
  W\!\left(\frac{p+p'-N}{kU}\right),
\]
since \(d=(p+p'-N)/k\) must be in the positive support. Fourier-invert the smooth test at length \(|k|U\). Decompose both true prime polynomials in their actual residue modulo \(|k|\) into the continuous principal profile divided by \(\varphi(|k|)\) and a centered error \(E_{v,a}\). Only units occur, as the large prime inputs exceed \(|k|\). The double principal term is exactly
\[
   X B_{|k|}(N)\int W(t/U) I(kt/X)\,dt
\]
with the \(B\)-factor from the [previous identity](DirectGoldbachGRHFullTopTargetAtom.md).

For mixed errors, summing the centered vector over residues \(a\) for which both \(a,N-a\) are units is an exact inclusion–exclusion over divisors \(e\mid |k|\). The surviving divisors give ordinary centered true-prime errors at the single reduced residue \(N\bmod e\); reduction of the continuous means is exact by the unit lift count. GRH with partial summation bounds this sum by \(O(\tau(|k|)\sqrt X L^{O(1)}(1+X|\beta|))\). The other continuous polynomial satisfies \(\int |V_v(\beta)|(1+X|\beta|)\,d\beta=O(1)\). Thus after the multiplier \(|k|U\,\widehat W(|k|U\beta)\) and the divisor \(\varphi(|k|)\), each mixed error is \(O(U\sqrt X\,\tau(|k|)L^{O(1)})\).

For clarity, the needed short-frequency bound on the two centered vectors is
\[
 \sum_a\int_{|\beta|\le b}|E_{v,a}(\beta)|^2d\beta
       \ll Xb L^{O(1)},\qquad X^{-1}\le b\le c_0/k^2.
 \tag{2}
\]
Use the corrected exponentially smoothed [Languasco–Perelli estimate (25)](https://www.research.unipd.it/retrieve/e14fb267-6015-3de1-e053-1705fe0ac030/%5B3%5D.pdf) for each character, and Dirichlet character Parseval (dividing by \(\varphi(|k|)\)). Here \(|k|\le O(X/U)\ll\sqrt X/L^{K/4}\). In passing to the compact smooth \(v\), write \(v(t)=e^{-t}a(t)\) and convolve with \(\widehat a(z)\) at shift \(z/X\). For \(|z|\le c_1 X/k^2\) the enlarged radii still lie on the smoothed estimate's rail (choose \(c_0,c_1\) small). For larger \(|z|\), the weighted GRH prefix bound \(O(\sqrt X L^{O(1)}(1+Xb+|z|))\) is sufficient: \(Xb\ll X/k^2\ll |z|\), and rapid decay pays the tail. In squared norm this gives only \(O(XbL^{O(1)})\), with no unabsorbed factor of \(X\). True prime powers can be removed per character by their total mass \(O(\sqrt X L^{O(1)})\), consistent with (2). This establishes the pure-prime bound.

For the quadratic term use Cauchy and (2) on dyadic \(|z|=|k|U|\beta|\) up to \(c_0U/|k|\), starting with the radius corresponding to \(|z|\le1\). If that radius is below \(1/X\), enlarge by a fixed factor since \(|k|U=O(X)\). With \(|k|U\) from the multiplier, each bound is \(O(X L^{O(1)}|z|\sup|\widehat W(z)|)\), so the smooth dyadic sum costs \(O(X L^{O(1)})\). Outside the rail \(|z|\gg U/|k|\), the pointwise GRH prefix bound after residue Parseval gives squared norm \(O(XL^{O(1)}(1+X|\beta|)^2)\). But \(X|\beta|=X|z|/(|k|U)\ll |z|^2\) there, because \(U^2\gg X\). Thus rapid decay again gives \(O(X L^{O(1)})\) or better. This last check is important at a log scale; a trivial \(O(X)\) bound on each individual character followed only by log-length Fourier truncation would leave an unacceptable power of \(X\).

Summing the mixed and quadratic errors over all \(1\le |k|\ll X/U\) costs \(O((X^{3/2}+X^2/U)L^{O(1)})=O(X^{3/2}L^{O(1)})\) on each dyad. Use the ordinary mean of \(\tau(k)\), not its maximum. After normalization and the sum over \(m\le M\) and dyadic intervals the total is \(O(X^{3/2} L^{O(1)}/Q)=O(X L^{-K+O(1)})\), which beats the smaller budget. Every logarithmic exponent needed here can be fixed independently of the sufficiently large \(K\), since the dyadic window derivatives are uniformly bounded.

## 3. Finish the identity and specify the remaining sign

The complement of the true prime–prime part of \(H_d\) is the same explicit lattice subtraction as in the prior note. Its arithmetic error \(O(X^{3/2}L^{O(1)}\tau(d)/\varphi(d))\) sums with \(1/Q\) to \(O(X^{3/2}L^{O(1)}/Q)\) using the ordinary divisor harmonic moment. The same exact \(B_k\) Euler expansion and Poisson average give the off-target main equal to the lattice reference minus the single model diagonal \(X\mathfrak S(N)I(0)\); the tail in the auxiliary Euler divisor gets a power saving since \(X/d\ge Y=\sqrt X/L^K\). The bounded-variation replacement of the weighted \(B_d/d\) sum by its integral costs \(O(X^2 M L^{O(1)}/(QT))\), again below the reduced budget. The true \(k=0\) term is left untouched, and restores the exact coefficient \(\kappa\); restoring its \(m\)-tail costs \(O(X L^{O(1)}/M)\) by the elementary actual Goldbach upper sieve. All these errors are \(o(XT/Q)\). Thus the full smooth top is \(\kappa(R(N)-X\mathfrak S(N)I(0))+o(XT/Q)\).

The missing coefficient is \(\asymp T/Q\) by the exact atom normalization and the positive small-\(q/Q\) limit of \(C_{q/Q}\) and mean of \(\varphi(q)/q\). For the low moduli \(q\le2Y\), the real Fourier multiplier of the exact kernel is uniformly Schwartz at scale \(qQ\). Apply the same corrected GRH squared bound on bands at that scale before \(q^2|\beta|\) reaches its rail, and then the GRH prefix/rapid-decay argument above. Gauss numerator averaging gives \(|D_q|\ll (X/Q)L^{O(1)}\), since \(q X/(qQ)=X/Q\), and \(Q/q\gg L^{2K}\) on this low range. Their sum is \(O(Y^2 L^{O(1)})=o(XT/Q)\). For \(q>2Y\) the kernel is constant and (2) of the prior note with \(|H_d|\ll XL^{O(1)}\) gives \(|D_q|\ll(X/Q)L^{O(1)}\sigma_{-1}(q)\). Its sum below \(T/L^B\) is negligible by the elementary mean of \(\sigma_{-1}\). Restoring the already-paid pole and mixed families leaves exactly the band in (1).

The ordinary absolute bounds on that band are still larger than \(XT/Q\) by positive powers of \(L\). Formula (1) therefore locates a smaller-scale pointwise signed problem; it does not prove that \(R(N)\) is positive.
