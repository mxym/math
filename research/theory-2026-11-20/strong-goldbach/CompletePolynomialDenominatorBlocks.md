# A fixed-target signed bound for complete polynomial-denominator blocks

The complete numerator sum retains the individual target's Gauss phase. This controls a polynomial-size family of separated genuinely minor windows with an absolute power saving, not by summing the logarithmic single-window estimate. It does **not** estimate the full minor term.

Let \(N\) be even, \(X=N-1/2\), \(L=\log X\), and use the unconditional actual zeta-zero weights \(B_*\), separated positive-ordinate band \(\mathcal B_X\), and smooth aperture \(G,w\) from [the cardinal-band theorem](UnconditionalCardinalZetaBand.md). Take \(H=X^{7/18}\), and a real even \(F\in C_c^\infty((-2,2))\) equal to one on \([-1,1]\). For \(s\in\mathbb T\) write
\[
 Z(s)=\sum_{\mathcal B_X} B_*\sum_{k\in\mathbb Z}F\big(H[(\gamma+\gamma')/X-2\pi(s+k)]\big).
\]
For a positive integer \(q\) the full paired denominator block is
\[
 Z[q]=\sum_{a\bmod q}^{*}\{Z(a/q)+Z(a/q+1/2)\}.                          \tag{1}
\]
Possible repetitions in (1) are intentional. For odd \(q\) its two numerator sets have denominators \(q,2q\); for \(4\mid q\) the two sets coincide, while for \(q\equiv2\pmod4\) the pairing duplicates the block for its odd part. The spectral weights themselves are the same across all blocks. Fix \(0<\epsilon<1/100,\ 0<\delta<1/9-\epsilon\), and put \(Q=X^{1/9-\epsilon}\). Uniformly at all even targets,
\[
      \sum_{q\le Q:\ q/(q,N)\ge X^\delta}|Z[q]|\ll_{\epsilon,\delta} X^{1-c},\qquad
      c=\min(\epsilon\delta/1000,10^{-5}).                               \tag{2}
\]
This includes every (not necessarily squarefree) denominator coprime to \(N\) in \([X^\delta,Q]\). There are at most \(\tau(N)X^\delta\) integers \(q\le Q\) failing the displayed divisor test, since they are of the form \(d k\) with \(d\mid N,\ k<X^\delta\). This counts **denominators**, not rational numerators. Nothing here says their signed sum is negligible. Distinct reduced centers with denominator at most \(2Q\) are spaced by \(\gg Q^{-2}\), wider than the individual packets. For a concrete example take \(\epsilon=1/1000,\delta=1/200\): all prime denominators in \([X^{1/100},2X^{1/100}]\) except those dividing \(N\) are in (2), as are all composite denominators there with \(q/(q,N)\ge X^{1/200}\). Each such reduced center and its parity mate is well outside the \(X^{-1/6-o(1)}\) neighborhoods of polylog-denominator rationals for large \(X\).

## 1. Actual cell transfer and two short windows

Replace each \(Z(s)\) by its ordinary-circle integral
\[
 \int_0^1 G(2\pi\alpha)F_s(\alpha)e(N\alpha)S_w(-\alpha)S_g(-\alpha)\,d\alpha,
 \quad F_s(\alpha)=\sum_k F(2\pi H(\alpha-s-k)),
\]
where \(S_v(\alpha)=\sum_p(\log p)v(p/X)e(p\alpha)\), \(e(x)=e^{2\pi ix}\), and \(g=1\) near the reflected support of \(w\), smooth with fixed compact support inside \((.6,.74)\). The proof of [the all-mesh transfer](MinorPacketDelocalization.md) applies to each translated test at this \(H\): the signed off-critical-line Taylor terms cost \(O(X^{.62})\) using the actual short sum-ordinate support, Ingham's weighted second moment and stationary phase. No complete set of equally spaced centers was used for that per-window bound. Use a logarithmic delay cutoff \(|s_{\rm delay}|\le2HX^\xi\), with \(0<\xi<\epsilon/10\). The arithmetic curvature, aperture, and weight errors cost \(O((H^2X^{3\xi}+HX^{2\xi})L^2+\sqrt X L^2)\) per window. Originally the Taylor expansion was through order 24, more than enough here since \(H X^\xi/X<X^{-.60}\); Schwartz tails can be taken to arbitrarily high powers depending on \(\xi\). Summing even the **absolute** transfer errors over \(O(Q^2)\) numerator/alias occurrences costs \(O(X^{1-\epsilon})\), since \(H^2Q^2=X^{1-2\epsilon}\), and \(.62+2/9<1\).

Because both prime variables in their fixed supports are odd and \(N\) is even, the product \(e(N\alpha)S_w(-\alpha)S_g(-\alpha)\) is half-periodic. Periodizing \(G\) therefore turns the paired integral at \(a/q,a/q+1/2\) **exactly** into twice the integral at \(a/q\) with \(G\) omitted. This is why no numerator-dependent smooth factor remains inside the finite Gauss transform.

Choose real even smooth compact Fourier factors \(F_1=F,\ F_2=1\) on the support of \(F\) (with \(F_2\in C_c^\infty\)); hence \(F=F_1F_2\). Let \(b_i(v)=(2\pi)^{-1}\int F_i(t)e^{-itv}dt\). These Schwartz functions have mass one. The inverse transform of \(F\) is exactly \(b_1*b_2\). Define the normalized vector entries, for \(i=1,2\), \(v_1=w, v_2=g\),
\[
 A_{i,\chi}(m)=H^{-1}\sum_p (\log p)v_i(p/X)\chi(p)b_i((p-m)/H).
\]
On central primes \(p\gg X\) there is no character-induction correction for any \(q\le Q\). All characters induced from a given primitive character therefore give **identical** \(A_{i,\chi}\); the principal case is the conductor-one vector entry. Fourier inversion on the finite rational numerator, or direct convolution in \(m\), gives the paired block integral exactly as
\[
 2\int_{\mathbb R}\sum_{a\bmod q}^* e(Na/q)\Big(\sum_{\chi\bmod q}V_{a\chi} A_{1,\chi}(m)\Big)
                   \Big(\sum_{\psi\bmod q}V_{a\psi} A_{2,\psi}(N-m)\Big) dm,              \tag{3}
\]
where \(V_{a\chi}=\varphi(q)^{-1}\sum_{b\in(\mathbb Z/q)^*}\overline{\chi(b)}e(-ab/q)\). Indeed the integral of the two \(H^{-1}b_i\) windows has kernel \(H^{-1}(b_1*b_2)((p+p'-N)/H)\), exactly the inverse Fourier coefficients of the translated flat top, with its rational modulation shown separately. The integral can be cut to a fixed smooth central \(m/X\)-window where \(m,N-m\asymp X\), with arbitrarily power-small total cost, by the support of \(w,g\), Schwartz tails, and the fact that only polynomially many characters/moduli occur.

## 2. A weighted conductor norm and a sparse exceptional spectrum

Write \(d_\chi\) for the primitive conductor and \(D_{\chi}=|\tau_q(\bar\chi)|/\sqrt{\varphi(q)}\) on the character space modulo \(q\). One has \(D_\chi^2\le d_\chi/\varphi(q)\): the induced Gauss sum is the primitive Gauss sum times \(\mu(q/d_\chi)\overline{\chi^*}(q/d_\chi)\), up to the harmless fixed sign in \(V\). The character matrix on the units is unitary after division by \(\sqrt{\varphi(q)}\). Thus (3) is a bilinear form in \(D A_1,D A_2\) with matrix \(U\) of operator norm at most one (in fact one, after harmless phases have been filled in); transpose in the bilinear, not Hermitian, expression does not change this bound. Its individual entries satisfy
\[
 |U_{\chi\psi}|\le \frac{\sqrt{q(q,N)}}{\varphi(q)}.                       \tag{4}
\]
Indeed they are phases times \(\varphi(q)^{-1}\sum_{a}^*\chi\psi(a)e(Na/q)\). For \(q=p^v\), a character of conductor \(p^b\), \(1\le b\le v\), gives zero unless \(v_p(N)=v-b\), and then magnitude \(p^{v-b}\sqrt{p^b}\). A principal local character instead gives the Ramanujan sum, also \(\le\sqrt{p^v(p^v,N)}\). The general bound follows by CRT, whose unit factors do not affect those magnitudes. In (2), (4) is \(\ll X^{-\delta/2}\log\log X\).

The multiplicities of induced characters cost only logarithms in the **weighted** norm:
\[
 \sum_{q\le Q:\,d\mid q}d/\varphi(q)\ll (\log Q)(\log\log(3Q)).         \tag{5}
\]
Use \(q/\varphi(q)\ll\log\log(3q)\) and sum \(d/q\). Each primitive character induces only one character per such modulus. Formula (5) includes the principal conductor \(d=1\); there is no unweighted factor \(Q\) from copying a pole.

Put \(\eta=\delta/20\), \(T=X^{11/18+\epsilon/4}\), so that \(Q^2T=X^{5/6-7\epsilon/4}\). For each primitive character of conductor \(\le Q\), declare its rare modes to be its nontrivial zeros with \(\beta>1-\eta, |\gamma|\le T\). Include the principal pole as one additional rare mode. At each \(q\) retain in \(A^{\rm b}_{i,\chi}\) the explicit-formula contributions of these modes (and the pole for the principal character). Write \(A^{\rm g}=A-A^{\rm b}\). These need not be positive summands. The following global estimates use no zero-free region and no RH:
\[
\begin{split}
 &\sum_{d\le Q}\sum_{\chi\bmod d}^* X^{-1}\int |A^{\rm g}_{i,\chi}|^2dm\ll X^{-2\epsilon\eta+o(1)},\\
 &\sum_{d\le Q}\sum_{\chi\bmod d}^* X^{-1}\int |A^{\rm b}_{i,\chi}|^2dm\ll L^{O(1)},
 \qquad \#\{\text{all rare modes counted with multiplicity}\}\ll X^{2\eta+o(1)}.          \tag{6}
\end{split}
\]
The central windows in (6) may be the reflected central window for the second prime. We give quantitative details because a logarithmic estimate for a single modulus would not justify (2).

Use the compact smooth explicit formula and the log-\(m\) local zero count/Schur argument proved in [the adaptive companion](AdaptiveZetaSingularSeries.md), now applied also to arbitrary subsets of the nontrivial zeros. With the fixed multiplier \(v_i(p/X)\) included in the Mellin integral the same derivative bounds hold, and the pole is \(H^{-1}\int v_i(y/X)b_i((y-m)/H)dy\), bounded. The normalized integral for any zero subset is bounded by a constant times
\[
 \sum_{\rho\ {\rm selected}} X^{-2(1-\beta)}(1+|\gamma|H/X)^{-D_0}\log(2q(2+|\gamma|)).
\]
A fixed smooth central majorant is implicit. The trivial-zero cost per character is negligible. On removing proper powers the normalized mean absolute error per character is \(O(X^{-1/2}L^2)\) by integrating the absolute kernel around each power; the normalized short sum over those powers is pointwise \(O(L)\) by the trivial integer bound. Thus its mean square costs \(O(X^{-1/2}L^3)\) per character, still power-small after multiplication by \(Q^2\). Choose \(D_0\) depending on \(\epsilon\); the height tail above \(T\) costs \(O(X^{-2})\) in total by ordinary dyadic zero counts since \(TH/X=X^{\epsilon/4}\). The zeros at \(\beta<1/2,|\gamma|\le T\) contribute at most \(O(Q^2 T X^{-1}L^2)\), power-small.

For the remaining zeros, [Koukoulopoulos (1.2), recording Montgomery–Huxley's classical hybrid density bound](https://dms.umontreal.ca/~koukoulo/documents/publications/shortaps.pdf), gives \(\sum_{d\le Q}\sum_{\chi}^* N(\sigma,T,\chi)\ll (Q^2T)^{(12/5+\epsilon)(1-\sigma)}L^{14}\) for \(1/2\le\sigma\le1\). Here \((5/6-7\epsilon/4)(12/5+\epsilon)<2-3\epsilon\). Partial summation against \(X^{-2(1-\sigma)}\) through \(1-\eta\), including its lower boundary, gives a saving of \(X^{-3\epsilon\eta}L^{O(1)}\); through 1 it gives at most a power of \(L\). Evaluating the density estimate at \(1-\eta\) bounds the number of rare zeros, as asserted. Add the pole once and absorb logarithms and the negligible proper-power errors: this gives (6). No count of how many conductors have exceptional zeros has been assumed.

## 3. Complete block estimate

Extend each part of (6) to all imprimitive entries weighted by \(D_\chi^2\) via (5). For terms of (3) with at least one good vector, the operator norm of \(U\) followed by Cauchy–Schwarz in \(m,q\) bounds the sum of the absolute block contributions by \(O(X^{1-\epsilon\eta+o(1)})\). The polynomial saving on the good side survives the polylogarithmic total mass of the other side, including the pole.

For the rare–rare term at each \(q\), there are at most \(X^{2\eta+o(1)}\) character coordinates with nonzero rare parts: every such coordinate has a rare inducing mode, and each primitive character occurs at most once at that modulus. On vectors supported on at most \(M\) coordinates on each side the bilinear norm is at most \(M\max|U_{ij}|\). Thus the rare–rare term costs, after summation using (4)–(6),
\[
                         O(X^{1-\delta/2+2\eta+o(1)}).
\]
This is where the oscillating target factor \(e(Na/q)\) and its **complete numerator sum** are indispensable. No bound for the sum of the absolute individual numerator-window contributions is inferred. Combining the estimates and the cell-transfer error proves (2) with the stated slack. The count of divisor-locked denominators follows from the elementary factorization above.

The input is classical hybrid zero density and a finite Gauss transform. MPR, [arXiv:2608.14777, Theorem 1.1](https://arxiv.org/abs/2608.14777), instead bounds individual prime exponential sums in terms of \(\max(q,qX|\alpha-a/q|)\); taking absolute values there does not retain the complete target-phase cancellation used in (4). In the current elementary treatment, ordinary hybrid density reaches \(Q^2T<X^{5/6-c'}\) with \(T\gtrsim X/H\), whereas near-continuous Farey coverage would require \(Q^2/H\) of order one, giving \(Q^2T\gtrsim X\). Accordingly (2) leaves a genuinely polynomial gap in coverage as well as the divisor-locked group. One cannot deduce Goldbach by completing that gap by a density argument over targets.

### Distinct-center union and comparison

The distinct-center union of denominators through \(Q\), augmented by \(2d\) for odd \(d\le Q\), is a disjoint union of the center sets underlying \(Z[d]\) for odd \(d\le Q\) and \(\frac12 Z[d]\) for \(4\mid d\le Q\); the latter notation divides the *multiplicity*, not the center. For even \(N\) and odd \(d\), the divisor test \(d/(d,N)\) equals \(2d/(2d,N)\). Consequently only blocks failing the divisor test can contribute a macroscopically negative net among the retained rational complete blocks. This says nothing about such blocks' actual sign, or the rest of the circle.

[Bhowmik–Grimmelt's 2026 major-arc formula](https://doi.org/10.1007/s10476-026-00191-z) also uses sums involving Dirichlet characters and the target, in an ordinary major-arc setting. [Li–Liu, arXiv:2610.26756v1](https://arxiv.org/abs/2610.26756v1) control an exceptional set using a minor-arc fourth moment under a fixed zero bound. The claim here is instead an unconditional upper bound for the complete signed paired blocks of the specified compact zeta selection at one target. No priority claim is made.
