# Exact removal of the reflected semiprime atom by a complementary prime tag

This gives a different fixed-target projection of the actual doubly high signed ledger. The whole large reflected-prime tag sum is represented by a **nonnegative rank-three-or-higher tag weight multiplied by the opposite original score**. In particular the previously exhibited positive bare semiprime-by-semiprime packet disappears pointwise from this new ledger. The price is an explicit score-negative debt; no small bound on that debt, or Goldbach conclusion, is asserted.

## 1. Statement

Keep the short smooth kernels \(h,f\) and physical conventions of [SpectralSubcriticalPrimeProduct](SpectralSubcriticalPrimeProduct.md): \(N=2x\), \(L=\log x\), \(s\) is true prime in the original \(x^{.10}<s<x^{.14}\), \(n=sq\in(x/2,x]\), \(m=N-n\), and \((n,N)=1\). Use all genuine distinct \(p\mid q,\ p>x^{.359}\), on the \(q\)-composite leg, with normalized weight \(\log p/\log q\). The two scores are the literal \(H_h(q)\), \(H_f(m)\), with positive support at most \(.001\), \(h=1\) and \(f(t)=1-t\) near zero. Let \(b\) be fixed with \(.501<b<2/3\), for example \(b=.502\). For composite \(m\), set
\[
 U_b(m)=\sum_{\substack{r\mid m\\r\ {\rm prime}\\r>x^b}}\log r,\qquad
 V_b(m)=\sum_{\substack{v\mid m\\v\ {\rm prime}\\m/v>x^b}}\log(m/v),
 \qquad D_b(m)=V_b(m)-U_b(m).
\]
Each prime is counted once, regardless of its exponent. The \(m/v\) in \(V_b\) is the actual integer quotient, **not assumed prime**. Then for every \(A>0\) and every even target,
\[
 \begin{split}
 &\sum_{\substack{s,q,p\\q,m\ {\rm composite}}}
    W_s(q)\frac{\log p}{\log q} H_h(q)H_f(m) U_b(m)\\
 &\hspace{1.1cm}=-
   \sum_{\substack{s,q,p\\q,m\ {\rm composite}}}
    W_s(q)\frac{\log p}{\log q} H_h(q)H_f(m) D_b(m)
      +O_{A,h,f,b}(xL^{-A}).                                           \tag{1}
 \end{split}
\]
The \(p\) sum may instead be restricted to any fixed exponent subinterval of the allowed band. No \(p\)-size upper cutoff below its genuine proper-divisor limit is required. Equation (1) is an **alternative accounting** of the entire \(r>x^b\) term of the same \(.359,.499\) projected ledger. Outside \(r>x^b\) the original narrow reflected band remains as before; if earlier removals are used in that band, use only their intersections there. Do not also spend any prior removals within \(r>x^b\) after taking (1).

For all sufficiently large \(x\), \(D_b(m)\ge0\) for composite \(m\); it vanishes exactly for \(\Omega(m)=2\) and is strictly positive for \(\Omega(m)\ge3\), with multiplicity allowed in \(\Omega\). In particular it is zero on both orientations of every true reflected semiprime, including the entire bare-semiprime \(m\) packet identified in [DoubleHighPositiveMassBarrier](DoubleHighPositiveMassBarrier.md).

## 2. The true complementary tag has zero signed mean at each target

We prove that the complete sum on \(V_b\), with the other factors in (1), is \(O_A(xL^{-A})\). Open its actual prime tag \(v\mid m\), and put \(q=p u,\ u\ge2\). Since \(p>x^{.359}\) exceeds the support of the \(h\)-divisors, the original \(H_h(q)\) is exactly \(\sum_{d\mid u}\mu(d)h(\log d/\log q)\). Do not include the missing \(u=1\) atom. The reflected \(v\) may be inside the \(f\)-support, so split its actual prime bit:
\[
 H_f(m)
 =\sum_{\substack{e\mid m/v\\(e,v)=1}}\mu(e)
    \left[
        f\!\left(\frac{\log e}{\log m}\right)-
        f\!\left(\frac{\log e+\log v}{\log m}\right)
    \right].                                                         \tag{2}
\]
This is exact also for repeated \(v\). Write \(Q=v e\), so the true congruence is \(n\equiv N\pmod Q\), with
\(Q\le (1.5x)^{1.001}x^{-b}\), strictly below \(x^{1/2}\) by a fixed power. The target masks are \((Q,N)=1\), \((p,N)=1\), and \((s u,N)=1\). The nonunit possibilities \((p,Q)>1\) or \((s,Q)>1\), including \(v=p\) or \(v=s\), are automatically excluded in the actual congruence; they are excluded as well by the coprime principal. At most \(\omega(Q)\) possible \(v\)-labels have the same \(Q\). The condition \(m/v>x^b\) is the exact moving integer endpoint \(n<N-vx^b\).

The \(n\)-source is the actual \(p\cdot(su)\), with a true prime Siegel–Walfisz \(p\)-sequence and a divisor-bounded \(su\)-sequence. On contributing central dyads both lengths are polynomial, since \(p>x^{.359}\) and \(su\ge s>x^{.10}\). Use [Maynard's full-scale two-factor convolution Bombieri–Vinogradov, Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733). Use its literal coprime model \(1_{(n,Q)=1}/\varphi(Q)\), with the actual target residue \(N\), not an unconditioned density. The prime \(p\) remains prime, with the independent target mask and optional log weight; its SW condition with an auxiliary coprimality parameter follows by removing the primes of that mask and ordinary prime Siegel–Walfisz/partial summation, as in [WrightSupercriticalPrimeProduct](WrightSupercriticalPrimeProduct.md). The composite \(su\)-coefficient retains \(u\ge2\), and no primality is imposed on \(u\).

For clarity, sharp moving endpoints do not cost a modulus-sized error. Clamp \(N-vx^b\) to the central window and round it to a grid of spacing \(xL^{-K}\). In the intervening interval at fixed \(Q\) each unweighted opened source at \(n\) is bounded by \(\tau(n)^C L^{O(1)}\) for fixed \(C\), even after its true \(s,p,d\) labels are included. For a reduced progression modulo \(Q\ll x^{1/2-c}\), the short-interval divisor bound with the modulus in fixed power reserve gives \(O(xL^{-K+O(1)}/\varphi(Q))\), uniformly in the endpoint. This is the classical Shiu divisor upper as in [Fouvry–Radziwiłł, Lemma 2.2](https://arxiv.org/pdf/1812.00562v2). It also bounds the analogous unprogressioned coprime model at each \(Q\), multiplied by \(1/\varphi(Q)\). Sum over \(Q\), paying only the harmonic \(\sum_{Q\le x}1/\varphi(Q)\ll L\) and the logarithmic number of labels at a given modulus. Choose \(K\) large, and use a smooth cutoff for each rounded prefix with the same error estimate; the central endpoints can be handled the same way. There are only \(L^{O(K)}\) prefixes, covered by the arbitrary log reserve.

The remaining continuous weights separate by compact Fourier expansion in the normalized dyadic logarithms of \(s,d,v,e,n\). The \(n\)-phase splits on \(p\) and \(su\), the \(s,d\) phases remain inside \(su\) by summing over genuine \(s\) and \(d\mid u\), and the \(v,e\) phases remain with their exact \(Q\)-label. This includes both terms of (2) and the literal \(W_s(q)\log(m/v)/\log q\). The separate \(\log p\) is on the true prime axis. Derivatives, truncation of the Fourier twists at log-sized heights, and dyads incur only log powers by the same proof as in the Wright unmarked note. The modulus coefficients are bounded by log powers, not a factor \(x^{.001}\); the BV error is summed over actual moduli before undoing the separations. This justifies replacement by the centered coprime model with arbitrary log reserve.

## 3. Coprime principal, including the short \(u\) end

Undo the model's dyads, Fourier integrals and prefix approximations with their controlled errors. At fixed \(s,p,v,e\), discard \((sp,NQ)>1\) as required by the true model. The smooth test in \(n=s p u\) retains \(x/2<n\le x\), \(m/v>x^b\), (2), the original \(W_s(q)\), and the original tag/log denominators. Its bounded variation is \(L^{O(1)}\) uniformly on the allowed interval, allowing the sharp endpoints by partial summation. Apart from the one \(h\)-divisor factor it is independent of \(d\). The inner principal, multiplied outside by \(1/\varphi(Q)\), is
\[
 \sum_{\substack{u\ge2\\(u,NQ)=1}}
       \Psi(s,p,v,e;s p u)
       \sum_{d\mid u}\mu(d)\,h\!\left(\frac{\log d}{\log(pu)}\right).      \tag{3}
\]
Write \(U=x/(s p)\), so the actual central interval has \(u\asymp U\). If \(U\le x^{\eta}\) for a sufficiently small fixed \(\eta>0\) depending only on the flat neighborhood of \(h\), every divisor of any \(u\) in (3) lies in that neighborhood after normalization by \(\log(pu)\ge(.86+o(1))L\). Thus (3) is **exactly zero** since \(u\ge2\). This handles the high-\(p\) end without accidentally including \(u=1\).

For \(U>x^\eta\), split the \(d\)-opening at \(D=\sqrt U\). For \(d\le D\), write \(u=d k\) and count coprime \(k\) by inclusion-exclusion in \(NQ\) with floor \(O(\tau(NQ)L^{O(1)})\) for the smooth test. The total floor is \(U^{1/2}x^{o(1)}\). The density involves the finite harmonic \(\sum_{d\le D,(d,NQ)=1}\mu(d)h(\log d/\log(pu))/d\) at a fixed continuous \(u\). The exact derivative of \(h\) is supported at polynomial \(d\), and the truncated upper-end cumulative value at \(D\) also has arbitrary log reserve. Hence the short-\(d\) main is \(O_A(U L^{-A})\), using uniform coprime Möbius harmonic PNT. For \(d>D\), first fix \(k\ll \sqrt U\), \((k,NQ)=1\), then bound the genuine signed Möbius sum in \(d\) over its actual moving interval. All such \(d\) are polynomially long, its weight has bounded variation \(L^{O(1)}\), and the uniform coprime Möbius PNT gives \(O_A((U/k)L^{-A})\). Summing \(k\) preserves arbitrary log reserve. These two Möbius PNT variants are uniform in polynomial \(NQ\): convolve \(\mu\) (or \(\mu(d)/d\)) with the multiplicative indicator of numbers supported on primes of the mask (or its reciprocal-weight version), split the convolution at the square root of the summation endpoint, and bound the tail by Rankin at exponent \(1/4\). The absolute short convolution harmonic mass costs only log powers. This also shows rigorously why an \(O(\tau(NQ))\) floor for every original \(d\le x^{.001}\) would be an unnecessary loss near this high-\(p\) end.

Thus (3) is \(O_A(U L^{-A})\) uniformly for every contributing choice of \(s,p,v,e\), including the power-small floors. Finally \(\sum_{s,p}U\ll xL^{O(1)}\) by harmonic summation and \(\sum_{v,e}1/\varphi(v e)\ll L^{O(1)}\). Therefore the entire signed \(V_b\) term is zero to arbitrary log reserve, proving (1).

## 4. Exact rank and sign of the new weight

For central \(m\) there is at most one true prime \(r>x^b\), and it cannot repeat. If it exists and \(z=m/r\), any true prime factor \(v\mid z\) is eligible for \(V_b\), with \(\log(m/v)\ge\log r\). For \(z\) prime this is the unique eligible \(v\), and equality holds. For \(z\) composite each such \(v<z\), giving strict inequality. If there is no high \(r\), \(U_b=0\); with \(\Omega(m)\ge3\) its least prime is at most \(m^{1/3}\), so \(m/v\ge m^{2/3}>x^b\) for that \(v\). With \(\Omega(m)=2\) and neither prime high, there is no eligible quotient. This proves the claimed bare-rank deletion including squares.

For squarefree \(m\) the literal signed weight has the more precise form
\[
 \frac{D_b(m)}{\log m}
       =\omega(m)-1-{\bf1}_{P^+(m)>x^b}
         -\sum_{\substack{\ell\mid m\ {\rm prime}\\
                         m/x^b\le\ell\le x^b}}
                   \left(1-\frac{\log\ell}{\log m}\right).              \tag{4}
\]
This follows by summing \(1-\log\ell/\log m\) over all prime factors first and assigning each omitted factor exactly its written amount. If there is a high \(r\), the middle sum is empty and the normalized weight is exactly \(\omega(m)-2\). For general \(m\), \(0\le D_b(m)\le\omega(m)\log m\).

The upper-bound debt in (1) is now precisely
\[
 {\cal D}_b(N)=
   \sum_{\substack{s,q,p\\q,m\ {\rm composite}}}
       W_s(q)\frac{\log p}{\log q}\,
       [-H_h(q)H_f(m)]_+\,D_b(m),                                     \tag{5}
\]
not a bound for the old all-positive bare semiprime packet. The complete projected sum equals this positive contribution **minus** the contribution with \(H_h(q)H_f(m)>0\), up to the established log error. A proof of a sufficiently small (5), or a bound keeping that negative compensation, is still needed; neither is implied by (1).

One may choose the fixed kernels with \(0\le h(t),f(t)\le1\) on their nonnegative arguments, preserving their required near-zero data and calibrations. Then a negative score on either leg requires at least two **distinct** primes in its short support: with no prime there the score is 1, and with just one it is \(1-h(\log\ell/\log q)\) or \(1-f(\log\ell/\log m)\). In particular in (1) all summands with \(\Omega(q)\le3,\ p\le x^{.85},\ \Omega(m)\le3,\ P^+(m)\le x^{.997}\) are nonpositive on the new side. Two active short primes on \(q\) would force \(q\le x^{.85+.002+o(1)}\), contrary to \(q\gg x^{.86}\). On \(m\), two would force \(m\le x^{.997+.002+o(1)}<x\). The pointwise statements cover repeated prime factors because the divisor scores use only distinct primes.

A uniform repeated-small-label bound is available, but it does not certify the budget. For fixed small \(\kappa\) the absolute contribution weighted by \(\omega(m)\log m\) of any event with two distinct factors \(\le x^\kappa\) on the same leg is
\[
        O_{h,f}(\kappa^2 M_N+x^{.98}).
\]
Indeed in the corrected-Henriot argument of [BilateralSmoothRoughReduction](BilateralSmoothRoughReduction.md), Section 2, extract both exact valuations on that leg. They are independent prime-power divisibility conditions, and with powers at most \(x^{.08}\) the free interval is shortened by their product but remains polynomially long. The resulting primitive linear forms have determinant \(N\); the same root exclusions, local factors, and uniform height hypothesis apply. Larger extracted powers have the prior power-small floor cost. At fixed Fourier parameter \(\xi\) or \(\eta\), opening the two actual primes costs two factors \(\sum_{\ell\le x^\kappa,\nu\ge1}a_\xi(\ell)/\ell^\nu\ll\kappa|\xi|\) (or the reflected analogue). To include \(\omega(m)\), dominate it by \(2^{\omega(m)}\), so the reflected local coefficient is at most doubled and still fits the same uniform multiplicative bounds; the extra fixed powers of the Fourier frequency are integrable since \(h,f\) are \(C^\infty_c\). The normalized sum of \(p\)-weights is at most 1. Thus (5) has a genuine two-small-factor scope and admits that kind of bound with fixed kernel constants. Those constants depend on the kernel widths and derivative norms, so inserting a support of \(.001\) does not prove a numerical cap of \(.010 M_N\), and taking kernel widths to zero does not justify treating the constants as fixed.

The comparison is on actual same-target \(q,m\) rows and does not assume independence of their prime factors. It moves the main unsolved sum to reflected rank at least three, with positive contributions requiring actual score negativity, rather than proving those contributions canceled or sufficiently small.
