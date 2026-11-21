# Complete δ blocks at a polynomial far scale: three large conductors and a dense target-phase covariance

These are unconditional deletion estimates for the **centered–centered** sector of the [fixed-target exact δ identity](ExactDeltaLinearRemoval.md). They do not evaluate the surviving sign, or posit zero-freeness. Fix \(0<\delta<1/4\), \(Q=X^{1-\delta}\), \(Y=X/Q=X^\delta\), \(N=X\) even, \(L=\log X\), and the fixed prime and δ weights of the linked identity. For any \(A>0\), there exist fixed \(C,K,C_0>0\) (\(C_0\) can be absolute) such that, to additive error \(O_{A,\delta}(XL^{-A})\), the total quadratic term \(\sum D_q\) there is the sum of:

1. the **entire genuine small sector** \(q\le Y L^C\), left intact here;
2. a covariance on \(Q/L^C<q\le Q\), restricted to \((q,N)\le \exp(K(\log L)^2)\). Both input characters have primitive conductor \(>Q/L^K\), and the product character has conductor \(>q\exp(-C_0 L/\log L)\).

In 2 one can further discard **any** adaptive masks of character pairs with at most \(q^{1/2-\eta}\) entries in each row and column, for any fixed \(\eta>0\), even if the masks depend on the target and prime data. All assertions preserve the complete numerator phase. There is no estimate for the unrestricted remaining matrix. We prove the successive deletions directly, not by claiming projections commute for arbitrary masks. Bounds below are uniform in all large targets; constants may depend on the fixed weights.

## 1. Exact spectrum and constant physical kernel

Write \(w_1=w,w_2=g\), \(P_{i,\chi}=\sum_p(\log p)w_i(p/X)\chi(p)-1_{\chi=\chi_0}X\int w_i\), for characters modulo \(q\). The sum uses only primes larger than \(Q\), so each centered sum depends only on its primitive inducing character. Put \(F_{a\chi}=\chi(a)/\sqrt{\varphi(q)}\) and \(V_{a\chi}=\varphi(q)^{-1}\sum_{r(q)}^*\bar\chi(r)e(-ar/q)=F_{a\chi}g_\chi\), where the scalar \(g_\chi\) has magnitude \(|\tau_q(\bar\chi)|/\sqrt{\varphi(q)}\). Then \(\sum_\chi V_{a\chi}P_{i,\chi}=S_i(-a/q)-\mu(q)X\int w_i/\varphi(q)\) with the ordinary prime sum \(S_i\). For \(q>2Y\), \(|p+p'-N|/(qQ)<1/2\) on both supports, also for continuous integration variables there, and \(\psi((p+p'-N)/Q^2)=1\). Thus the physical kernel is exactly the constant \(C_{q/Q}=\sum_j\omega(qj/Q)/j\ge0\) throughout the integral. The exact quadratic block is
\[
 D_q=\frac{c_Q C_{q/Q}}{qQ}(gP_1)^t U_q(gP_2),\quad
 U_q=F^t\operatorname{diag}(e(aN/q))F,quad
 (U_q)_{\chi\psi}=\varphi(q)^{-1}\sum_{a(q)}^*(\chi\psi)(a)e(aN/q).\tag{1}
\]
The formula is bilinear; norm upper bounds use usual absolute values and the unitary matrix \(U_q\). We only use fixed bounds for \(C_x,c_Q\). For all \(q\) the pole model in the linked identity still sums to \(X\mathfrak S(N)\int w+O_\delta(X^{1-c_\delta})\): truncate at \(q\le X^{\delta/2}\), use \(H/X=q/Y\) and uniform kernel mass there, and its Rankin bound with exponent \(1/2\) on the tail. The complete mixed terms still sum to \(O_A(XL^{-A})\) in absolute value: for \(q\le D=\sqrt X/L^{B(A)}\) the same maximal Bombieri–Vinogradov argument applies (all \(H\), bounded variation). At \(q>D\) the mixed test is exactly \(C_{q/Q}(X/(qQ))w_i\int w_{3-i}\). The progression discrepancy for its unscaled fixed prime test and any \(d|q\) is \(\ll XL/d\) by trivial counting (and \(d/\varphi(d)\ll\log\log X\)). The divisor formula for the mixed block therefore gives \(\ll X^2 L\tau(q)/(qQ\varphi(q))\). The sum past \(D\) is \(\ll X^2 L^{O(1)}/(QD)=o(XL^{-A})\) by the divisor first moment. The high block in (1) is consequently quadratic in actual centered arithmetic quantities, not an unevaluated linear major term.

## 2. Middle and divisor-locked moduli

For \(D<q\le2D\), \(q>2Y\), put \(E_i(D)=\sum_{q\sim D}(qQ)^{-1}\sum_\chi |g_\chi P_{i,\chi}|^2\), restricting to \(q\le Q\). Finite Parseval identifies the inner sum exactly with \(\sum_a^* |S_i(-a/q)-\mu(q)X\int w_i/\varphi(q)|^2\). The additive large sieve for points separated by \(\gg D^{-2}\), and \(\sum_{p\asymp X}(\log p)^2\ll XL\), give
\[
 E_i(D)\ll L^3 X\left(\frac{X}{D Q}+\frac DQ\right).\tag{2}
\]
The subtracted principal weights cost \(\ll X^2( DQ)^{-1}\sum_{q\sim D}1/\varphi(q)\ll X^2\log\log X/(DQ)\). Use unitary Cauchy in (1) followed by Cauchy in \(q\). Summing (2) over the middle dyadics \(YL^C<q\le Q/L^C\) costs \(O(XL^{4-C})\), and over the top dyadics \(Q/L^C<q\le Q\) it costs \(O(XL^4)\); the \(X/(DQ)\) there is power-small. Here and below cutting dyadic end intervals cannot worsen the positive quadratic norm estimates.

For top moduli divisible by a specific \(m\), every pair of distinct reduced fractions from that subfamily is separated on the circle by \(\gg m/D^2\). This follows by writing the two denominators as \(mk,mk'\); it includes distances modulo one. Replacing \(D^2\) by \(D^2/m\) gives the analogous bound \(\ll XL^3(X/(DQ)+D/(mQ))\), since the pole cost can still be bounded by its previous unrestricted value. Sum over all \(m|N\) greater than \(Z=\exp(K_0(\log L)^2)\), to dominate all top \(q\) with \((q,N)>Z\). The \(X/(DQ)\) term times \(\tau(N)=X^{o(1)}\) is power-small, and
\[
 \sum_{m|N,\ m>Z}m^{-1}\le Z^{-1/\log L}\prod_{p|N}(1-p^{-1+1/\log L})^{-1}\ll L^{-K_0}(\log L)^{O(1)}.
\]
For \(p\le 2L\) the logarithm of the product is \(O(1+\sum_{p\le2L}1/p)=O(\log\log(3L))\). Larger primes cost \(O(1)\), since \(p^{-1+1/\log L}\ll L^{-1}\) there and \(\omega(N)\ll L\). Summing the dyadics gives arbitrary logarithmic savings for the energy of these moduli by choosing \(K_0\) large. Cauchy again removes them from (1). These are genuine divisor-lock estimates even when \(N\) is divisible by many small primes.

## 3. Low inducing conductors in the two input vectors

For the character induced by primitive \(\chi^*\bmod d\) we have \(|g_\chi|^2\le d/\varphi(q)\) by the standard formula \(\tau_q(\bar\chi)=\mu(q/d)\bar\chi^*(q/d)\tau_d(\bar\chi^*)\), with an inessential conjugation on the scalar. Each primitive character induces at most once per multiple. Since a multiple occurs only for \(d\le2D\),
\[
 \sum_{q\sim D:\,d|q}\frac{d}{qQ\varphi(q)}\ll\frac{\log\log X}{DQ}.
\]
Thus for \(d\le R=Q/L^{K_1}\), the restricted top energy on this dyadic is
\[
 \ll\frac{XL^3}{DQ}(X+R^2),\tag{3}
\]
by the multiplicative large sieve for primitive characters, applied to the fixed prime coefficients. Subtracting the sole primitive pole \(d=1\) adds at most the indicated \(X^2\) term. Summing (3) over \(D\ge Q/(2L^C)\) gives arbitrary log savings by increasing \(K_1\) after \(C\), since \(Q^2\gg X^{3/2}\). Terms with either low input are removed by Cauchy and the full top energy (2). After removal, each side is just a diagonal projection of its vector, with no larger energy. In the statement take \(K\) large enough for both cutoffs (increasing either constant only reduces the size of the deleted set).

## 4. Low conductor of the **product** and sparse interactions

For each \(d|q\), restrict the entries of \(U_q\) to \(\operatorname{cond}(\chi\psi)|d\). Up to inversion of one character index this is a convolution matrix on the character group of \((\mathbb Z/q)^*\). Finite Fourier diagonalization shows its operator norm equals
\[
 \max_{b\in(\mathbb Z/d)^*}\left|\frac{\varphi(d)}{\varphi(q)}\sum_{a(q)^*,\ a\equiv b(d)} e(aN/q)\right|.\tag{4}
\]
Indeed retaining characters that factor modulo \(d\) projects the Fourier symbol onto functions of the reduced class modulo \(d\). The map on unit groups is onto; there is no condition at nonunits, and all included fibers have equal size. Under CRT the additive factors acquire only unit scalars in the numerator. Locally for \(p^v\Vert q,\ u=v_p(d)>0\), summing over the \(p^{v-u}\) lifts yields modulus \(1_{p^{v-u}|N}\), including \(u=v\). At \(u=0\) the factor has modulus \(|c_{p^v}(N)|/\varphi(p^v)\). In particular (4) is at most \((q/d,N)/\varphi(q/d)\).

By Möbius inversion, the mask of exact product conductor \(r|q\) is the sum over \(d|r\) of these conductor-dividing masks with weights \(\mu(r/d)\). For \((q,N)\le Z\), the operator restricted to product conductor \(r\le q\exp(-C_0L/\log L)\) has norm at most
\[
 \tau(q)^2 Z (\log\log X)\exp(-C_0 L/\log L).\tag{5}
\]
Here \(q/d\ge q/r\), \((q/d,N)\le Z\), and \(m/\varphi(m)\ll\log\log(3m)\). The classical divisor bound \(\tau(q)\le\exp((\log2+o(1))L/\log L)\) uniformly for \(q\le X\) makes (5) smaller than every negative power of \(L\), for example for \(C_0=4\). Applying (5) to the already input-projected vectors and using (2) discards their entire low-product piece.

Finally every individual matrix entry has modulus \(\le\sqrt{q(q,N)}/\varphi(q)\). Locally a character of conductor \(p^b\) with \(b>0\) gives zero unless \(v_p(N)=v-b\), in which case the unnormalized Gauss magnitude is \(p^{v-b+b/2}\); for \(b=0\) use the Ramanujan sum. Multiply by CRT. On remaining top moduli this is \(q^{-1/2+o(1)}\). For any mask with \(\le q^{1/2-\eta}\) entries per row and column the Schur bound is \(q^{-\eta+o(1)}\); intersecting it with the remaining product-conductor condition cannot increase those counts or its largest entry. This argument applies **after** the product cut and the input projections, so no unjustified multiplication of Schur multiplier norms is needed. Equation (2) completes the proof.

The surviving term is an actual bilinear correlation: its phase is the full \(e(aN/q)\), not a diagonal primitive-character second moment. Neither the ordinary nor the [Conrey–Iwaniec–Soundararajan asymptotic large sieve](https://arxiv.org/abs/1105.1176) supplies a sign for it. All top moduli have at most \(O(X/q)=X^{\delta+o(1)}\) nonzero aliases in the two-prime sum. In the **unrestricted** exact block the arithmetic target atom occurs with coefficient \(\lambda_q=c_Q\varphi(q)C_{q/Q}/(qQ)\), \(\lambda_q\ll Q^{-1}\), \(\sum_q\lambda_q=1\) by (1) of the linked note at \(k=0\). Thus a single missing target can affect many blocks coherently. The deleted cross-character matrices here are genuinely small operators on centered prime vectors; the remaining aggregate has no established positivity.

For comparison, [Bhowmik–Grimmelt (2026), §§6–7](https://doi.org/10.1007/s10476-026-00191-z) discuss generalized singular series in conventional major arcs, where small product conductor can be important. The deletion here is instead for the specified high moduli in an exact smooth delta representation, using the finite conditional-expectation norm and sparse actual denominator sets. The low delta sector is explicitly not evaluated.
