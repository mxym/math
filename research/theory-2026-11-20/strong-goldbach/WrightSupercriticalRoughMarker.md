# A complete supercritical cofactor-marker gate with \(p<r\)

The [unmarked supercritical dispersion sector](WrightSupercriticalPrimeProduct.md) needs the true \(p\) to be longer than \(r e\), which cannot hold when \(p<r\). On a genuinely different physical sector the long Siegel–Walfisz source can be the **product of two actual primes \(p w\)**, with \(w\) a prime factor of the true cofactor \(u=q/p\). An exact Ramaré extraction removes the multiplicity, and a maximum marker-rank inequality leaves enough free range for the original signed principal to vanish. This is a complete at-least-one gate, not a count with the original row charged once per potential marker.

## 1. Physical statement

Use all definitions, unit masks, and unchanged short kernels \(h,f\) of [WrightSupercriticalPrimeProduct](WrightSupercriticalPrimeProduct.md). In the actual double-high sum let \(q=p u\), \(m=r v\), and impose the independent exponent boxes
\[
  .123\le\log_x s\le.125,\quad
  .491\le\log_x p\le.492,\quad
  .5095\le\log_x r\le.5105,\qquad
  I=(x^{.02098},x^{.02102}).
\]
Assume the actual \(u\) has at least one prime divisor in \(I\). Then the whole contribution, with its literal \(W_s(q)\), \(H_h(q)\), \(H_f(m)\) and normalized true tag weights \(\log p/\log q,\log r/\log m\), is \(O_{C,h,f}(xL^{-C})\) for any fixed \(C\), uniformly in the even target \(N=2x\).

Here \(p<r\) and \(pr\ge x^{1.0005}\) on every row. Neither large prime is changed. Both true original cofactors are polynomially long. This gate is disjoint from the unmarked \(p>r\) result and the subcritical result, and the original row is counted exactly once on the gate, no matter how many distinct eligible \(w\) it contains.

## 2. Moving the real grouped source into range

Put \(j=u/w\) for a chosen actual \(w\in I,w\mid u\). Write
\[
  G_I(j)=\frac1{1+\omega_I(j)},\qquad
  \omega_I(j)=\#\{w'\in I:\ w'\ \mathrm{prime},\ w'\mid j\}.
\]
Temporarily remove every physical \(n\) having \(w^2\mid n\) for any prime \(w\in I\). Their number is at most
\(\sum_{a\in I\cap\mathbf Z}(O(x/a^2)+1)\ll x^{1-.02098}+x^{.02102}\).
Arbitrary fixed divisor powers in the bilateral weights leave a strict power saving on this removed set; the analogous model cost is also power-small using \(\sum_Q1/\varphi(Q)\ll L^{O(1)}\). In the remaining arithmetic sum the exact identity is
\[
 {\bf1}_{\omega_I(u)>0}
          =\sum_{\substack{w\mid u\\w\ \mathrm{true\ prime\ in}\ I}}G_I(u/w).
                                                                    \tag{1}
\]
One may allow all \(j\ge1\) on the right, without imposing a coupled \((w,j)=1\) mask in dispersion: any extra row is on the same already bounded squareful set. Source multiplicities are polynomially bounded by divisor functions throughout. This explains why the independent coefficient on \(j\) is \(G_I(j)\), not a weight depending on the varying original \(w\).

Keep \(r\) in the actual modulus \(Q=r e\) with \(e\) from the \(f\)-score. The actual progression is now
\[
           n=(p w)(s j)\equiv N\pmod Q .
\]
Both short scores open as before: all \(p,w,r\) exceed the respective short divisor cutoffs, and the \(h\)-score divisor \(d\) divides \(j\), not the chosen \(w\). Also \(d,e\) both have size at most \(x^{.001+o(1)}\). The signed modulus remains real and still has a unique \(r\) label. Preserve the target-unit masks on both source factors and the modulus. The same compact Fourier separation of \(s,d,e,n\) from the unmarked note applies, with \((p w)^{it}(s j)^{it}\) on the product phase; the \(s\) and \(d\) sums enter the short divisor-bounded coefficient, as does \(G_I(j)\) upon writing \(j=b/s\). The separated \(\log p\) weight goes on the grouped \(p w\) factor, and the \(\log r\) weight on the modulus. All central smoothing, Fourier tails, and absolute model costs are controlled by the same divisor moments as in the unmarked theorem.

The grouped long factor \(p w\) satisfies the required Siegel–Walfisz property with its written \(\log p\) factor and the Fourier twist. To see this in [the precise Fouvry–Radziwiłł Definition 1](https://arxiv.org/pdf/1812.00562v2), fix \(w\) and the auxiliary coprimality parameter. Nonunit \(w\) at the progression modulus or the auxiliary integer is absent for both actual and modeled reduced counts. For unit \(w\), a fixed product interval gives exactly an interval for the genuine prime \(p\); use ordinary prime Siegel–Walfisz, partial summation in \(p\) for the log-sized Fourier twist, and remove the primes dividing the target or the auxiliary integer at the cost of their number. For moduli at most a sufficiently large log power this is \(O_A(P L^{-A}\tau_k(\text{auxiliary integer}))\) after allowing the log weights, where \(P\asymp p\) is the long prime's own scale. For larger moduli use the elementary \(O(P/Q+1)\) bound at each reduced residue and the reciprocal-totient principal. Summing over actual primes \(w\) costs at most the length \(W\) of their dyad; \(P W\) is the required full SW source scale. The two prime bands are disjoint and the coefficient is divisor-bounded, after removing an overall \(O(L)\) factor if necessary. There is no independence assumption about the original fixed-target prime pairs.

In [Wright's moving-residue rail with the bounded constant-factor \(|a|/Y\) extension](WrightSupercriticalPrimeProduct.md), the long slot exponent is \(\lambda=\log_x(p w)\in[.51198,.51302]\), the full product size \(Y\asymp x\), and the modulus exponent is in \([.5095,.5115]+o(1)\). The worst upper rail gap is \(.51198-.5115=.00048\). The first lower rail has worst left side \(34(.51302)-17=.44268<.5095\), and the auxiliary lower rail has \((23/8)(.51302)-1<.475<.5095\). The short slot \(1-\lambda\) stays above \(3/8\). These strict rails apply to every genuine dyad; \(a=N\) remains the same integer throughout. Thus the true sum can be replaced by the coprime centered main, with arbitrary log reserve, even after restoring all separated weights and size dyads.

## 3. Exact reciprocal multiplicity in the centered principal

On the central \(n\)-window,
\[
       .383+o(1)\le\log_x u\le .386+o(1).
\]
Since \(19(.02098)=.39862>.386\), at most 18 distinct \(I\)-primes divide \(u\). In the model, any \(j=u/w\) has at most 17 distinct \(I\)-primes, even after allowing \(w\mid j\) again, since \(j\le x^{.386-.02098+o(1)}\) and \(18(.02098)>.386-.02098\). Use the exact finite negative-binomial coefficients
\[
  G_I(j)=\int_0^1 t^{\omega_I(j)}\,dt
         =\sum_{i=0}^{17}\frac{(-1)^i}{i+1}\binom{\omega_I(j)}i.
                                                                    \tag{2}
\]
For fixed \(i,s,p,r,e,w\), open the binomial as subsets of \(i\) distinct primes from \(I\) dividing \(j\), with product \(A\). Open \(h\) on \(d\mid j\) independently. Since \(d<x^{.001+o(1)}\), \((A,d)=1\), and \(j=A d k\) exactly. The true \(w\) may also divide \(A\) in the restored model; this does not affect \((A,d)=1\) or the primary count, and (1) was only asserted off the power-small repeat set. The congruence has already been replaced by its modeled coprimality, not discarded prematurely: for each \(Q=r e\), discard nonunit \(s,p,w,A\) at \(NQ\), and keep \((d,NQ)=(k,NQ)=1\). The primes \(s,p,w,A\) cannot share \(e\) by size, nor equal \(r\) in these boxes, but exclusions at \(N\) are still literal.

Every \(k\)-interval in this principal retains fixed power room. Even when all possible marks are present,
\[
 s p\,w A\,d\le
 x^{.125+.492+18(.02102)+.001+o(1)}=x^{.99636+o(1)}.                  \tag{3}
\]
The central test on \(n=s p w A d k\) now has the same bounded-variation counting integral as in the unmarked proof. Replacing the coprime \(k\)-sum by a density gives the measure \((\varphi(NQ)/(NQ))\,dy/(s p w A d)\) with an error bounded by \(\tau(NQ)L^{O(1)}\) per fixed tuple. By (3), summing the tuple errors costs \(x^{.99636+o(1)}\): the product \(w A\) with at most 18 prime factors has at most the fixed divisor-order multiplicity after grouping, and the \(r,e\) harmonic mass divided by \(\varphi(Q)\) costs only log powers. All 18 terms of (2) are genuinely finite and the bound is unconditional.

In the integral, after restoring the actual limits, the \(d\)-axis again has no dependence except \(1/d\) and the exact \(h(\log d/\log (y/s))\) test and fixed \((d,NQ)=1\). Its coprime Möbius harmonic vanishes to arbitrary log reserve by exact near-zero flatness. This is true for each fixed tuple of opened \(I\)-primes, including the \(i=17\) term. The other labels have only harmonic polylogarithmic mass. This proves the stated exact gated cancellation.

An example of genuinely positive raw profiles in this gate is \(s\) near exponent \(.124\), \(p\) near \(.4915\), \(r\) near \(.5100\), and \(u=w k\) with \(w\) near \(.021\) and \(k\) actual prime near \(.3635\), while \(v\) is an actual prime near \(.490\). For sufficiently small fixed exponent neighborhoods, the five bands of \(q,m\) plus \(s\) are disjoint and every prime score is unchanged since none of the true factors enters either short score. Actual dyadic occupation follows by ordinary PNT on each side's last prime in the two chosen central product intervals; it is not presumed at an individual target.

The theorem removes this whole exact at-least-one sector, but says nothing about the unmarked complement when \(p<r\). In particular it gives no cancellation for the typical balanced semiprime \(q=p u\) if \(u\) is a single macroscopically sized prime (then the \(I\)-gate is empty). No portion of the original signed \(.010M_N\) criterion not explicitly covered here is estimated.
