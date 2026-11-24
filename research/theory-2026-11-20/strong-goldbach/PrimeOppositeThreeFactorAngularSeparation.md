# Middle-scale three-factor rows: a power-saving B-process–Robert–Sargos estimate

Research note, 2026-11-24. This resolves the previously recorded \(N^{1/2}\) **discrepancy** obstruction for an exact rank-three complement at true source scale \(H=\sqrt N\). It does not show that the total prime-source mass of rank three is smaller than the rough lower bound. A consequence we can pay is a simultaneous exclusion of the logarithmic-angle ties of the adjacent factors on a positive genuine rough cloud.

## 1. Precise thin-band assertion

Fix constants \(0<\alpha<\beta<1\), \(0<\mu<1/8\), and set \(H=N^{1/2}\), \(L=\log N\), \(z=N^\mu\). For a true row \(N-p=qrs\) with \(q\le r\le s\) and \(p\in(\alpha H,\beta H]\), divide \(q,r\) into dyadic boxes \([Q,2Q),[R,2R)\). Necessarily \(Q\le R,\ QR^2<N\); for a true \(z\)-rough row \(Q\ge z/2\). Put
\[
 W=\frac{N}{QR},\qquad
 u=\log_N Q,\quad v=\log_N R,\quad w=\log_N W=1-u-v.
\]
Thus \(u\le v\le w,\ v\le(1-u)/2\). Fix \(u_*=33/100<1/3\). In the whole range
\[
 Q\ge z/2,\quad Q\le R\le W,\quad u\le u_*,
\]
there exist fixed \(\lambda_0,\zeta>0\) such that, in every residue triple \((a_1,a_2,a_3)\bmod d\) with \(1\le d\le N^{\lambda_0}\), the number of integer triples
\[
 q\in[Q,2Q),\quad r\in[R,2R),\quad \alpha H<N-qrs\le\beta H
\]
is
\[
 \mathcal V/d^3+O(N^{1/2-\zeta})
                                                        \tag{1}
\]
uniformly; here \(\mathcal V\ll H\) is the real volume of the stated band with the source interval rounded to half-integers. We allow the enlargement dropping the order and the extra \(s\)-box; \(s\asymp W\) still holds. All constants are independent of the target \(N\), the modulus and its residue classes. This is a concordant-shifts power saving, and no primality is used in (1).

## 2. Reduction to a bilinear discrepancy in a true box

Write \(A=\lfloor\alpha H\rfloor+1/2\), \(B=\lfloor\beta H\rfloor+1/2\); for integer sources the exact condition is \(A<N-qrs<B\). Thus the \(s\)-interval has endpoints \((N-c)/(qr)\), \(c=A,B\), neither an integer for any integer positive \(q,r\). On the \(s\)-residue \(a_3\bmod d\), its two floor phases are
\[
 \frac{N-c}{d q r}-\frac{a_3}{d}.
\]
The main length term is \((B-A)d^{-1}\sum_{q\equiv a_1}q^{-1}\sum_{r\equiv a_2}r^{-1}\).
By monotonicity each arithmetic-progression sum near \(Q\) is \((\log2)/d+O(1/Q)\), similarly at \(R\). Thus the product gives \(\mathcal V/d^3+O(H/(d^2Q)+H/(dQR))\); this has a fixed power of saving because \(Q\ge z/2\). The remainder is the difference of two sawtooth sums, whether or not any one of the actual \(s\)-intervals has length exceeding one.

Use the elementary Erdős–Turán discrepancy inequality for the sequence over both \((q,r)\) variables. With a fixed \(0<\eta<\mu/8\), choose Fourier cutoff \(M_F=\lfloor Q N^{-\eta}\rfloor\). The truncation error is
\[
 O(QR/(d^2 M_F))=O(RN^\eta)=O(N^{1/2-\zeta_1})
\]
for a fixed \(\zeta_1>0\), since \(u\ge\mu/2\) and \(v\le(1-u)/2\) for large \(N\). The remaining term is bounded by the sum over dyadic \(K\) with \(K\ll M_F\) of
\[
 \sum_{h\asymp K}\frac1h
 \left|\sum_{\substack{q\sim Q,\ q\equiv a_1\bmod d\\
                       r\sim R,\ r\equiv a_2\bmod d}}
 e\left(\frac{h(N-c)}{dqr}-\frac{h a_3}{d}\right)\right| .
                                                        \tag{2}
\]
As usual one can take separate terminal partial dyadic intervals; all their constraints go in bounded coefficients below. The logarithmic weights in (2) are not allowed to become a three-way tensor. The following transform preserves the required separation.

## 3. Exact one-variable B transform in the \(r\)-progression

Use [Montgomery–Vaughan, *Multiplicative Number Theory II*, Theorem 16.20 / Corollary 16.21](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf), with the fourth-derivative refinement (16.50) of the ordinary B-process. The same result may be stated with integer-endpoint half weights plus \(O(1)\). Let \(D_0\) be a power of two with \(N^3\le D_0<2N^3\) (unrelated to the sieve modulus). Take real \(r\) endpoints \(r_-=R-1/D_0\) and \(r_+=2R-1+1/D_0\) so they contain exactly the desired integer interval. For \(r=a_2+d j\) let
\[
 f(j)=\frac{h(N-c)}{d q(a_2+d j)}-\frac{h a_3}{d}.
\]
On the actual \(j\) interval of length \(O(R/d)\), \(f'(j)=-h(N-c)/(q r^2)\), \(f''(j)\asymp h d W/R^2=:M_2>0\). Also \(f^{(3)}\ll M_2(d/R)\), \(f^{(4)}\ll M_2(d/R)^2\), with absolute constants from \(r\asymp R\), \(q\asymp Q\) and \(N-c\asymp N\). These bounds make the refined (16.50) terms \(O(1)\), even when \(M_2\) is large: the containing length is \(O(R/d)\) and \(d\ll R\). The B-process has error
\[
 O(\log(2+hW/R)+R/\sqrt{h d W}).
\]
No nonintegrality/gcd assumption on the endpoints or the frequency is needed for this bound. Summing it over \(q\), with the \(1/h\) weights and all frequency blocks, gives
\[
 O(Q L^2+QR/\sqrt W)
     \ll N^{\max(u,\,1-3w/2)+o(1)} .
\]
Since \(w\ge(1-u)/2\) and \(u\le u_*\), \(1-3w/2\le(1+3u_*)/4<1/2\).

For the transformed main sum use the positive integer \(\ell=-f'(j_\ell)\) at a stationary point. The exact condition is
\[
 \frac{h(N-c)}{q r_+^2}\le \ell\le \frac{h(N-c)}{q r_-^2}.
                                                        \tag{3}
\]
The phase and weight are respectively
\[
 \frac2d\sqrt{\frac{h\ell(N-c)}q}-\frac{\ell a_2+h a_3}{d}+\frac18,\qquad
 \frac{(h(N-c))^{1/4}}{\sqrt{2d}\,q^{1/4}\ell^{3/4}} .
                                                        \tag{4}
\]
They follow by substituting \(r_\ell=\sqrt{h(N-c)/(q\ell)}\) in \(f(j_\ell)+\ell j_\ell\) and \(1/\sqrt{f''(j_\ell)}\). Notice that the derivative frequency \(\ell\) is independent of the progression step \(d\) in its scale. For \(h\asymp K\) all \(\ell\)'s in (3) lie in \(O(1)\) dyadic intervals comparable to \(\Lambda=KW/R\ge K\). For \(h\) or \(\ell\) equal to 1 one may double that index (and include just even values by a coefficient) to fit exactly the convention \((H,2H]\) of the cited theorem, absorbing the corresponding fixed square-root factor in the phase. The same convention handles inclusion of the left endpoint of a physical \(q\) box; alternatively it splits off one smaller adjacent dyadic box. All scale comparisons are unchanged.

## 4. Legal separation of both moving endpoints

The transformed endpoint (3) cannot just be put into the pair \((h,\ell)\) coefficient, because it depends on \(q\). Here is an explicit separation avoiding that error. The endpoint conditions are the difference of two threshold functions \(1_{x>1}\) with
\[
 x=\frac{q\ell r_\pm^2}{h(N-c)},
\]
positive and comparable to 1 on the full relevant dyadic ranges. Both endpoints \(r_\pm\) have odd numerator over \(D_0\). Equality \(x=1\) would imply
\[
 2q\ell (D_0 r_\pm)^2=h(2N-2c)D_0^2.
\]
This is impossible by the 2-adic valuations: \(q\ell<N^2\) for large \(N\) since \(\ell\ll KW/R\ll N/R^2\) and \(q\ll Q\le R\), while the right side is divisible by \(D_0^2\). The difference is a nonzero rational with denominator at most \(O(hN D_0^2)\ll N^8\). Hence \(|x-1|\gg N^{-8}\) and \(|\log x|\gg N^{-8}\).

Write \(\sigma=1/L\). The truncated vertical Perron integral, equivalently the Fourier inverse of \(e^{-\sigma t}1_{t>0}\), gives
\[
 1_{x>1}=
 \frac{1}{2\pi i}\int_{\sigma-iN^{20}}^{\sigma+iN^{20}}
                   \frac{x^\xi}{\xi}\,d\xi+O(N^{-12}).
\]
The error follows from integration by parts on the tails, \(O(x^\sigma/(N^{20}|\log x|))\). The integral has total kernel absolute mass \(O(L)\). For each \(\xi\), the factor \(x^\xi\) factors exactly into a constant depending on cutoff and scales, a factor depending on \((h,\ell)\), and one depending on \(q\); using \(h/K,\ell/\Lambda,q/Q\) makes their moduli bounded by fixed constants. Its imaginary powers have modulus 1 independently of the truncation height. The ordinary B-amplitude in (4) similarly factors after dividing out the scale \(R/\sqrt{K d W}\). The extra phases \(-(\ell a_2+h a_3)/d+1/8\) belong to the pair coefficient; the true indicator \(q\equiv a_1\bmod d\) belongs to the single coefficient. Finally the full absolute-weighted block (2) can be taken by choosing one unit phase per \(h\) to align its transformed sum and including the bounded real \(K/h\) in that same pair coefficient, leaving a global \(1/K\). This works also for any truncated frequency block. The Perron errors are negligible even after summing over all \((h,\ell,q)\): there are \(O(K\Lambda Q)\ll N^2\) words in each block, the prefactor is \(O(R)\ll N^{1/2}\), and \(1/K\le1\). Thus the uniform per-word \(O(N^{-12})\) yields \(O(N^{-9})\) or better, before the harmless \(O(L)\) blocks.

## 5. Apply the original Robert–Sargos estimate and account for all exponents

Use [O. Robert and P. Sargos, *Three-dimensional exponential sums with monomials*, J. Reine Angew. Math. 591 (2006), 1–20](https://doi.org/10.1515/CRELLE.2006.012), [original PDF](https://perso.univ-st-etienne.fr/rool6510/robert-2006-crelle.pdf), Theorem 1 and (1.1), (1.3). In their notation **the single axis \(m\)** is the physical \(q\) of length \(Q\), with exponent \(\alpha_{\rm RS}=-1/2\); the two axes \(h,n\) are our frequencies \(h,\ell\) of lengths \(K,\Lambda\), both with exponent \(1/2\). Thus the required \(\alpha_{\rm RS}(\alpha_{\rm RS}-1)\beta_{\rm RS}\gamma_{\rm RS}\ne0\), the exponents are fixed reals (negative on the single axis is explicitly permitted), and their coefficient condition is exactly \(a(h,\ell)b(q)\) of bounded moduli. The original phase parameter is
\[
 X_{\rm RS}\asymp \frac{\sqrt{K\Lambda N/Q}}d
                  \asymp\frac{KW}{d}>1
\]
for large \(N\) as \(W\ge N^{(1-u_*)/2}\) and the modulus exponent is small. Constant perturbations from the half-integer \(c\) are absorbed by the *exact* real parameter \(N-c\) in the square root; the theorem is not being used for a translate of the monomial in its variables.

The four terms in (1.3) are \((X_{\rm RS}/(K\Lambda Q^2))^{1/4}\), \((K\Lambda)^{-1/4}\), \(Q^{-1/2}\), \(X_{\rm RS}^{-1/2}\), times \((K\Lambda Q)^{1+\epsilon}\). Including the B-process amplitude scale, the \(1/K\) in (2), and the \(O(L)\) separation cost gives at most
\[
 O_\epsilon\left(N^\epsilon Q\sqrt{KW/d}
   \left[
       \left(\frac{R}{dKQ^2}\right)^{1/4}
       +\left(\frac{R}{K^2W}\right)^{1/4}
       +Q^{-1/2}
       +\sqrt{\frac{d}{KW}}
   \right]\right),
                                                        \tag{5}
\]
where \(\epsilon>0\) may be made arbitrarily small (absorb the product-power loss and logarithms by reducing its input value). For \(t=\log_N K\), dropping only favorable powers of \(d\), the four exponents of \(N\) in (5), before the arbitrary epsilon, are exactly
\[
 \frac12+\frac{t-v}{4},\qquad
 \frac{1+3u}{4},\qquad
 \frac12+\frac{t-v}{2},\qquad
 u.
\]
The Fourier cutoff gives \(t\le u-\eta+O(1/L)\le v-\eta+O(1/L)\), and \(u\le u_*<1/3\). Hence all four have a uniform fixed saving below \(1/2\). This remains valid if the two smallest factors have the same logarithmic angle or if the latter two are very unequal; no separated-tail condition was used. Choose \(\epsilon\) much smaller than the minimum of these margins, sum \(O(L)\) blocks and both endpoints, and include the explicit truncation, endpoint and progression-integral errors. This proves (1). In particular there is no need to switch back to a higher-frequency untransformed estimate; \(M_F\) was already sufficient for the discrepancy.

## 6. Genuine prime-source consequence and what remains open

[The earlier curved-shell argument](PrimeOppositeThreeFactorCurvedShell.md) supplies the missing per-box power saving when \(u>u_*\): its discrepancy exponent for any dyadic \(Q_{\min}=Q\ge N^{u_*}\) is \(1-(3-\vartheta)u_*<1/2\), \(\vartheta=231/158\), since \(u_*>79/243\). Both arguments therefore overlap. For fixed \(Q,R\) there are only \(O(1)\) relevant third dyadic boxes, as \(qrs=N-p\), and the two methods give a uniform four-prime upper count
\[
 O(F_N(z)H/L^4)
\]
per actual dyadic shape \((Q,R)\). For (1) apply exactly the four-prime Selberg proof from [the three-factor curved-shell proof](PrimeOppositeThreeFactorCurvedShell.md) to the literal band, with polynomial \(qrs(N-qrs)\), \(d\le D=N^\lambda\) for fixed \(\lambda<\min(\lambda_0,\zeta/4)\), and its truncated inner Euler primes \(y\le z\). Its residue-count error is \(O(N^{1/2-\zeta}D^{3+o(1)})\), negligible after \(O(L^2)\) boxes. The local factors are identical to the curved proof, and yield the same target factor \(F_N(z)\). This step has no primes-in-short-interval input at the target scale.

For the genuine ordered rank-three points, either logarithmic-angle tie \(r/q\le N^\delta\) or \(s/r\le N^\delta\) forces the corresponding box exponents to satisfy respectively \(0\le v-u\le\delta+O(1/L)\) or \(0\le1-u-2v\le\delta+O(1/L)\). For each dyadic \(Q\), either strip leaves \(O(1+\delta L)\) dyadic \(R\)'s, and there are \(O(L)\) choices for \(Q\). The true bad rank-three sources thus cost at most
\[
 C\delta\,F_N(z)H/L^2 + o(F_N(z)H/L^2),
\]
with \(C\) independent of the final small fixed \(\delta\). The same bookkeeping can simultaneously pay [the prior \(z\)-rough squarefree and two-factor deletions](PrimeOppositeSquarefreeThirdFactor.md) by choosing \(\delta\) small compared to the rough lower constant. In particular a positive genuine prime-source cloud survives on which any exact rank-three complement must satisfy
\[
 r/q>N^\delta,\qquad s/r>N^\delta.
\]
At a purported no-pair target all surviving complements are genuine composites; this yields a structural restriction on their rank-three rows even in the middle range \([1/4,79/243]\).

This is a full-range **per-box** power saving for the exact rank-three thin band (or a positive majorant with that accuracy in the near-balanced curved-shell range), plus a positive-cloud exclusion of angular ties. It is **not** deletion of the whole rank-three family: \(O(L^2)\) boxes of arbitrary angles would cost \(O(F_N(z)H/L^2)\) with no coefficient less than the rough lower bound. Quantitative comparison of the full angular rank-three mass, and the higher-arity rows, are separate obstacles. No Goldbach representation or rank-two lower bound at source scale \(\sqrt N\) follows.
